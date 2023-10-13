#include "sat/sms/sms_proof_trim.h"
#include "sat/sat_types.h"
#include "sat/sms/sms_proof_trim.h"
#include "sat/sat_justification.h"
#include "sat/sat_proof_trim.h"
#include "sat/sms/sms_solver.h"
#include "util/hash.h"
#include "util/sat_literal.h"

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

sms_proof_trim::sms_proof_trim(params_ref const& p, ast_manager& man): m(man), m_var2Exp(m) {
    for(unsigned i = 0; i < 2; i++) {
        m_solvers[i] = alloc(solver, p, m.limit());
        m_solvers[i]->set_trim();
        m_solvers[i]->set_drat(false);
    }
}

sms_proof_trim::~sms_proof_trim() {
    //HACK to prevent integrity checker from checking consistency of learnt
    //clauses
    m_solvers[0]->set_conflict();
    m_solvers[1]->set_conflict();
    dealloc(m_solvers[0]);
    dealloc(m_solvers[1]);
}

void sms_proof_trim::add_var(unsigned i, expr_ref t) {
    unsigned v = m_solvers[i]->add_var(true);
    if (m_var2Exp.size() <= v) { m_var2Exp.resize(v + 1); }
    m_var2Exp[v] = t;
}

void sms_proof_trim::log_clause(status stat, unsigned sz, literal const *c, unsigned idx) {
    SASSERT(idx == NSOLVER_EXT_IDX_TMP || idx == PSOLVER_EXT_IDX_TMP);
    //log copied clauses as learned on the source solver as well
    if (stat.is_copied()) {
        log_clause(status::asserted(), sz, c, stat.get_src() - 1);
    }

    unsigned i = m_ctrail.size(), old_i, hash;
    literal_vector lc(sz == 0 ? 1 : sz);
    for(unsigned i = 0; i < sz; i++) lc[i] = c[i];
    std::sort(lc.begin(), lc.end());
    solver* s = m_solvers[idx];
    literal l, k;
    clause*  cidx;
    if (s->inconsistent()) {
        TRACE("satmodsat", tout << "solver " << idx << " already inconsistent, not adding " << lc << " of status " << stat;);
        return;
    }
    TRACE("satmodsat", tout << "logging " << lc << " status " << stat << " index " << m_ctrail.size() << " id " << idx;);
    switch (sz) {
        case 0:
            if (m_units[idx].find(null_bool_var, old_i)) break;
            m_units[idx].insert(null_bool_var, i);
            lc[0] = null_literal;
            m_ctrail.push_back(lv_st(lc, stat, nullptr, idx));
            break;
        case 1:
            SASSERT(c[0] != null_literal);
            if (m_units[idx].find(c[0].var(), old_i)) break;
            s->mk_clause(lc, status::redundant());
            m_units[idx].insert(c[0].var(), i);
            m_ctrail.push_back(lv_st(lc, stat, nullptr, idx));
            break;
        case 2:
            hash = hash_u_u(lc[0].hash(), lc[1].hash());
            if (m_binary[idx].find(hash, old_i)) break;
            s->mk_clause(lc, status::redundant());
            m_binary[idx].insert(hash, i);
            m_ctrail.push_back(lv_st(lc, stat, nullptr, idx));
            break;
        default:
            if (m_clauses[idx].find(lc, old_i)) break;
            cidx = s->mk_clause(lc, status::redundant());
            m_clauses[idx].insert(lc, i);
            m_ctrail.push_back(lv_st(lc, stat, cidx, idx));
            break;
    }
    s->propagate(false);
}

unsigned sms_proof_trim::get_clause_index(literal l, justification js, unsigned idx) {
    TRACE("satmodsat", tout << "getting reason for " << l << " with js "; m_solvers[idx]->display_justification(tout, js););
    literal j;
    literal_vector lc;
    switch (js.get_kind()) {
        case justification::NONE:
            if (js.level() != 0) return UINT32_MAX;
            SASSERT(l != null_literal);
            return m_units[idx].find(l.var());
        case justification::BINARY:
            j = js.get_literal();
            if (j < l) std::swap(l, j);
            return m_binary[idx].find(hash_u_u(l.hash(), j.hash()));
        case justification::CLAUSE:
            for (auto a : m_solvers[idx]->get_clause(js)) lc.push_back(a);
            std::sort(lc.begin(), lc.end());
            return m_clauses[idx].find(lc);
        default:
            SASSERT(false);
    }
}

void sms_proof_trim::get_dep_cp(literal_vector const& cl, vector<literal_vector>& op) {
    TRACE("satmodsat", tout << "getting dep for " << cl << "\n");
    auto& b = m_deps[cl];
    for (auto i : b) {
        const auto [lc, st, cidx, idx] = m_ctrail[i];
        if (st.is_copied() && st.m_src == NSOLVER_EXT_IDX_ORIG) {
            op.push_back(lc);
        }
        if (st.is_redundant() && idx == PSOLVER_EXT_IDX_TMP) {
            //TODO: cache
            get_dep_cp(lc, op);
        }
    }
}

void sms_proof_trim::mark_clause(unsigned i, literal_vector const& cl) {
    if (i == UINT32_MAX) return;
    auto [lc, st, cidx, idx] = m_ctrail[i];
    if (st.is_redundant() || st.is_asserted() || st.is_copied()) {
        mark(lc);
        SASSERT(lc != cl);
        auto& b = m_deps.insert_if_not_there(cl, vector<unsigned>());
        b.push_back(i);
    }
}

void sms_proof_trim::mark_dep_clauses(literal_vector const& cl, unsigned idx, unsigned start) {
    solver* s = m_solvers[idx];
    literal l = s->get_m_not_l();
    if (l != null_literal) {
        mark_clause(get_clause_index(l, s->get_justification(l.var()), idx), cl);
        l = ~l;
    }
    mark_clause(get_clause_index(l, s->m_conflict, idx), cl);
    for (unsigned i = s->m_trail.size(); i-- > start;) {
        literal l = s->m_trail[i];
        mark_clause(get_clause_index(l, s->get_justification(l.var()), idx), cl);
    }
}

void sms_proof_trim::rup(unsigned i) {
    auto [lc, st, cidx, idx] = m_ctrail[i];
    if (st.is_copied()) return;
    solver* s = m_solvers[idx];
    s->propagate(false);
    //solver already inconsistent
    //this clause is subsumed by another learnt clause
    if (s->inconsistent()) {
        unmark(lc);
        s->m_qhead = 0;
        s->m_inconsistent = false;
        return;
    }
    //WHy would it be null?
    if(is_null(m_ctrail[i])) return;
    s->push();
    justification js = justification(1);
    for(unsigned i = 0; i < lc.size(); i++) {
        SASSERT(lc[i] != null_literal);
        s->assign(~lc[i], js);
        if (s->inconsistent()) break;
    }
    unsigned init_qhead = s->m_qhead;
    if (!s->inconsistent()) s->propagate(false);
    //mark all clauses used to derive lc
    mark_dep_clauses(lc, idx, init_qhead);
    s->pop(1);
}

void sms_proof_trim::remove_from_sol(unsigned i) {
    auto [lc, st, cidx, idx] = m_ctrail[i];
    solver* s = m_solvers[idx];
    switch(lc.size()) {
        case 1: {
            s->m_assignment[lc[0].index()] = l_undef;
            s->m_assignment[(~lc[0]).index()] = l_undef;
            unsigned j = 0, sz = s->m_trail.size();
            literal l = lc[0];
            bool found = false;
            while(j < sz) {
                if (s->m_trail[j].var() == l.var()) found = true;
                else if (found) s->m_trail[j - 1] = s->m_trail[j];
                j++;
            }
            SASSERT(found);
            s->m_trail.shrink(sz - 1);
            s->m_qhead = 0;
            break;
        }
        case 2:
             s->detach_bin_clause(lc[0], lc[1], true);
             break;
        default:
            SASSERT(&cidx);
            s->detach_clause(*cidx);
            break;
    }
}

void sms_proof_trim::trim() {
    if (m_ctrail.empty())
        return;
    unsigned sz = m_ctrail.size();
    mark(m_ctrail[sz - 1]);
    m_deps.insert(std::get<0>(m_ctrail[sz - 1]), vector<unsigned>());

    for (unsigned i = sz; i-- > 0;) {
        dbg_print_trim(i);
        if (!is_marked(m_ctrail[i]) || is_input(m_ctrail[i])) continue;
        if (is_cp_null(m_ctrail[i])) {
            SASSERT(i != 0);
            m_deps.insert(std::get<0>(m_ctrail[i - 1]), vector<unsigned>());
            mark(m_ctrail[i - 1]);
            continue;
        }
        if (!is_null(m_ctrail[i]))
            remove_from_sol(i);
        TRACE("satmodsat", tout << "rup";);
        rup(i);
    }
    expr_ref_vector itp(m);
    for (unsigned i = m_ctrail.size(); i-- > 0;) {
        auto [lc, st, cidx, idx] = m_ctrail[i];
        if (!is_marked(lc)) continue;
        if (!is_fwd_cp(st)) continue;
        vector<literal_vector> op;
        get_dep_cp(lc, op);
        add_itp_imp(op, lc, itp);
    }
    TRACE("satmodsat", tout << "itp is " << itp;);
}

void sms_proof_trim::mk_clause(literal_vector const& clause, expr_ref& out) {
    expr_ref_vector lits(m);
    for(auto l : clause) {
        if (l == null_literal) lits.push_back(m.mk_false());
        else {
            expr* e = m_var2Exp[l.var()].get();
            expr_ref ne(m);
            ne = l.sign() ? m.mk_not(e) : e;
            lits.push_back(ne);
        }
    }
    mk_or(lits, out);
}

void sms_proof_trim::mk_tail(vector<literal_vector> const& lcc, expr_ref& out) {
    expr_ref_vector clauses(m);
    expr_ref clause(m);
    for(auto l : lcc) {
        mk_clause(l, clause);
        clauses.push_back(clause);
    }
    mk_and(clauses, out);
}

void sms_proof_trim::add_itp_imp(vector<literal_vector> const& tail, literal_vector const& head, expr_ref_vector& itp) {
    expr_ref tail_expr(m), head_expr(m), implies(m);
    mk_tail(tail, tail_expr);
    mk_clause(head, head_expr);
    mk_implies(tail_expr, head_expr, implies);
    itp.push_back(implies);
}
