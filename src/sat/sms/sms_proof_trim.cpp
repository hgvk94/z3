#include "sat/sms/sms_proof_trim.h"
#include "sat/sat_types.h"
#include "sat/sms/sms_proof_trim.h"
#include "sat/sat_justification.h"
#include "sat/sat_proof_trim.h"
#include "sat/sms/sms_solver.h"
#include "util/hash.h"
#include "util/sat_literal.h"


using namespace sat;

sms_proof_trim::sms_proof_trim(params_ref const& p, ast_manager& man): m(man) {
    m_solvers[0] = alloc(solver, p, m.limit());
    m_solvers[1] = alloc(solver, p, m.limit());
}

sms_proof_trim::~sms_proof_trim() {
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
    TRACE("satmodsat", tout << "logging " << lc << " status " << stat  << " index " << idx;);
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
    literal j;
    literal_vector lc;
    switch (js.get_kind()) {
        case justification::NONE:
            SASSERT(l != null_literal);
            return m_units[idx].find(l.var());
        case justification::BINARY:
            j = js.get_literal();
            if (j < l) std::swap(l, j);
            return m_binary[idx].find(hash_u_u(l.hash(), j.hash()));
        case justification::CLAUSE:
            for (auto a : m_solvers[idx]->get_clause(js)) lc.push_back(a);
            return m_clauses[idx].find(lc);
        default:
            SASSERT(false);
    }
}

void sms_proof_trim::get_dep_cp(literal_vector const& cl, vector<literal_vector>& op) {
    auto& b = m_deps[cl];
    for (auto i : b) {
        const auto [lc, st, cidx, idx] = m_ctrail[i];
        if (st.is_copied() && st.m_src == NSOLVER_EXT_IDX_TMP) {
            op.push_back(lc);
        }
        if (st.is_redundant() && idx == PSOLVER_EXT_IDX_TMP) {
            //TODO: cache
            get_dep_cp(lc, op);
        }
    }
}

void sms_proof_trim::mark_clause(unsigned i, literal_vector const& cl) {
    auto [lc, st, cidx, idx] = m_ctrail[i];
    if (st.is_redundant() || st.is_copied()) {
        mark(lc);
        auto& b = m_deps.insert_if_not_there(cl, vector<unsigned>());
        b.push_back(i);
    }
}

void sms_proof_trim::mark_dep_clauses(literal_vector const& cl, unsigned idx) {
    solver* s = m_solvers[idx];
    //TODO: process m_not_l as well
    SASSERT(s->m_not_l == null_literal);
    mark_clause(get_clause_index(null_literal, s->m_conflict, idx), cl);
    for (unsigned i = s->m_trail.size(); i-- > 0; ) {
        literal l = s->m_trail[i];
        mark_clause(get_clause_index(l, s->get_justification(l.var()), idx), cl);
    }
}

void sms_proof_trim::rup(unsigned i) {
    auto [lc, st, cidx, idx] = m_ctrail[i];
    if (st.is_copied()) return;
    solver* s = m_solvers[idx];
    bool pop = false;
    if (!s->inconsistent()) { pop = true; s->push(); }
    justification js = justification(1);
    for(unsigned i = 0; i < lc.size(); i++) {
        s->assign(~lc[i], js);
    }
    if (pop) s->propagate(false);
    //mark all clauses used to derive lc
    mark_dep_clauses(lc, idx);
    s->pop(1);
}

void sms_proof_trim::remove_from_sol(unsigned i) {
    auto [lc, st, cidx, idx] = m_ctrail[i];
    solver* s = m_solvers[idx];
    switch(lc.size()) {
        case 1:
            s->m_assignment[lc[0].index()] = l_undef;
            s->m_assignment[(~lc[0]).index()] = l_undef;
            break;
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
    for (unsigned i = m_ctrail.size() - 1; i >= 0; i--) {
        if (!is_marked(m_ctrail[i])) continue;
        remove_from_sol(i);
        rup(i);
    }
    for (unsigned i = m_ctrail.size() - 1; i >= 0; i--) {
        auto [lc, st, cidx, idx] = m_ctrail[i];
        if (!is_marked(lc)) continue;
        if (!is_fwd_cp(st)) continue;
        vector<literal_vector> op;
        get_dep_cp(lc, op);
        mk_horn(lc, op);
    }
}

void sms_proof_trim::mk_horn(literal_vector& v, vector<literal_vector>& op) {
    TRACE("satmodsat", for(auto a : op) tout << a; tout <<" ==> " << v;);
}
