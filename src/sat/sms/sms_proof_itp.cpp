#include "sat/sms/sms_proof_itp.h"
#include "ast/ast.h"
#include "ast/ast_util.h"
#include "sat/sms/sms_solver.h"
#include "util/sat_literal.h"
#include "util/vector.h"
using namespace sat;
namespace {
    void mk_not(expr* in, expr_ref& out) {
        ast_manager& m = out.get_manager();
        if (m.is_not(in)) out = to_app(in)->get_arg(0);
        else out = m.mk_not(in);
    }

    bool has_const(expr_ref_vector const& v, bool pol) {
        ast_manager&m = v.get_manager();
        for(auto l : v) {
            if (pol && m.is_true(l)) return true;
            if (!pol && m.is_false(l)) return true;
        }
        return false;
    }

    void rm_consts(expr_ref_vector &l, bool pol) {
        ast_manager&m = l.get_manager();
        unsigned sz = l.size();
        unsigned i = 0;
        for (auto a : l) {
            if (pol && !m.is_true(a)) l[i++] = a;
            if (!pol && !m.is_false(a)) l[i++] = a;
        }
        l.shrink(i);
        if (i < sz && i == 0) { l.push_back(pol? m.mk_true() : m.mk_false()); }
    }

    void mk_or(expr_ref_vector &l, expr_ref& out) {
        ast_manager& m = l.get_manager();
        rm_consts(l, false);
        if (l.empty()) {
            out = m.mk_true();
            return;
        }
        if (l.size() == 1) {
            out = l.get(0);
            return;
        }
        if (has_const(l, true)) {
            out = m.mk_true();
            return;
        }
        out = m.mk_or(l);
    }

    void mk_and(expr_ref_vector& l, expr_ref& out) {
        ast_manager& m = l.get_manager();
        rm_consts(l, true);
        if (l.empty()) {
            out = m.mk_true();
            return;
        }
        if (l.size() == 1) {
            out = l.get(0);
            return;
        }
        if (has_const(l, false)) {
            out = m.mk_false();
            return;
        }
        out = m.mk_and(l);
    }

    void mk_implies(expr_ref tail, expr_ref head, expr_ref& out) {
        ast_manager& m = tail.get_manager();
        if (m.is_false(tail) || m.is_true(head)) { out = m.mk_true(); return; }
        if (m.is_true(tail)) out = head;
        else if (m.is_false(head)) mk_not(tail, out);
        else out = m.mk_implies(tail, head);
    }
}
void sms_proof_itp::log_clause(status s, unsigned int sz, const literal *c) {
    literal_vector l(sz, c);
    if (sz == 0) l.push_back(null_literal);
    m_trail.push_back({s, l});
}

void sms_proof_itp::mk_clause(literal_vector const& clause, expr_ref& out) {
    expr_ref_vector lits(m);
    for(auto l : clause) {
        SASSERT(l == null_literal || is_shared(l.var()));
        if (l == null_literal) lits.push_back(m.mk_false());
        else lits.push_back(get_expr(l));
    }
    mk_or(lits, out);
}

void sms_proof_itp::mk_tail(vector<literal_vector> const& lcc, expr_ref& out) {
    expr_ref_vector clauses(m);
    expr_ref clause(m);
    for(auto l : lcc) {
        mk_clause(l, clause);
        clauses.push_back(clause);
    }
    mk_and(clauses, out);
}

void sms_proof_itp::add_itp_imp(vector<literal_vector> const& tail, literal_vector const& head, expr_ref_vector& itp) {
    expr_ref tail_expr(m), head_expr(m), implies(m);
    mk_tail(tail, tail_expr);
    mk_clause(head, head_expr);
    mk_implies(tail_expr, head_expr, implies);
    itp.push_back(implies);
}

void sms_proof_itp::interpolate(expr_ref& out) {
    vector<literal_vector> tail;
    expr_ref_vector itp(m);
    for(auto const& [st, lc] : m_trail) {
        if (!st.is_copied()) continue;
        if (st.get_src() == NSOLVER_EXT_IDX) {
            tail.push_back(lc);
            continue;
        }
        if (st.get_src() == PSOLVER_EXT_IDX) {
            add_itp_imp(tail, lc, itp);
        }
    }
    mk_and(itp, out);
    TRACE("satmodsat", tout << "interpolant is " << out << "\n";);
}
