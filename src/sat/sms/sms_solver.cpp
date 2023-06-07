#include "sat/sms/sms_solver.h"
#include "ast/ast_pp.h"
#include "sat/sat_justification.h"
#include "sat/sat_types.h"
#include "util/debug.h"
#include "util/lbool.h"
#include "util/sat_literal.h"
#include "sat/sms/sms_proof_itp.h"

using namespace sat;

/*
** ---- BEGIN ---- Methods to dump clausal proofs
*/

void sms_solver::dump(unsigned sz, literal const *lc, status st) {
  SASSERT(m_drating);
  switch (st.m_st) {
      case status::st::input:
          (*m_out) << "i " << get_id() << " ";
          break;
      case status::st::asserted:
          (*m_out) << "l " << get_id() << " ";
          break;
      case status::st::redundant:
          (*m_out) << "l " << get_id() << " ";
          break;
      case status::st::deleted:
          (*m_out) << "d " << get_id() << " ";
          break;
      case status::st::copied:
          (*m_out) << "c " << st.get_src() << " " <<  get_id() << " ";
          break;
  }
  dump_clause(sz, lc);
  if (m_itp) m_itp->log_clause(st, sz, lc);
}

void sms_solver::dump_clause(unsigned sz, literal const* lc) {
  SASSERT(m_drating);
  if (sz == 0) {
    (*m_out) << null_literal << "\n";
      return;
  }
  unsigned i = 0;
  for (; i < sz - 1; i++) (*m_out) << lc[i] << " ";
  (*m_out) << lc[i] << "\n";
  m_out->flush();
}

void sms_solver::drat_dump_cp(literal_vector const& cl, ext_justification_idx id) {
  SASSERT(m_drating);
  int src =
      id == NSOLVER_EXT_IDX ? m_nSolver->get_id() : m_pSolver->get_id();
  status st = status::copied();
  st.set_src(src);
  dump(cl.size(), cl.data(), st);
  m_out->flush();
}

void sms_solver::drat_dump_ext_unit(literal l, ext_justification_idx id) {
    sms_solver *s = id == NSOLVER_EXT_IDX ? m_nSolver : m_pSolver;
    SASSERT(s);
    status st = status::copied();
    st.set_src(s->get_id());
    literal_vector cl(1, {l});
    dump(1, cl.data(), st);
    m_out->flush();
}


/*
** ---- END ---- Methods to dump clausal proofs
*/

/*
** ---- BEGIN ---- Methods for clause learning
*/

// place literal with highest dl in cls at position 0
// returns level at which cls is asserting
unsigned sms_solver::place_highest_dl_at_start(literal_vector& cls) {
    if (cls.size() <= 1) return 0;
    unsigned lvl = 0;
    unsigned hl = 0;
    for (unsigned i = 0; i < cls.size(); i++) {
        if (lvl < m_solver->lvl(cls[i])) {
            hl = i;
            lvl = m_solver->lvl(cls[i]);
        }
    }
    std::swap(cls[0], cls[hl]);
    unsigned bj_lvl = 0;
    for (unsigned i = 1; i < cls.size(); i++) {
        bj_lvl = std::max(bj_lvl, m_solver->lvl(cls[i]));
    }
    return bj_lvl;
}

// add cls to solver, return ptr to the new clause
clause* sms_solver::learn_clause(literal_vector& cls) {
    dbg_print_lv("learning lemma", cls);
    literal_vector tmp(cls);
    m_validator->add_clause(tmp.size(), tmp.data(), sat::status::asserted());
    DEBUG_CODE(unsigned i = 1; for (; i < cls.size(); i++) SASSERT(m_solver->lvl(cls[i]) <= m_solver->lvl(cls[0])););
    return  m_solver->mk_clause(cls.size(), cls.data(), sat::status::redundant());
}

// learn clause (antecedent ==> l) from external solver idx
void sms_solver::learn_clause_and_update_justification(
    literal l, literal_vector const &antecedent, ext_justification_idx idx) {
    literal_vector cls;
    cls.push_back(l);
    for (auto a : antecedent) cls.push_back(~a);
    if (idx == NSOLVER_EXT_IDX) m_nSolver->validate(cls);
    else m_pSolver->validate(cls);

    if (m_drating) drat_dump_cp(cls, idx);
    place_highest_dl_at_start(cls);
    clause* c = learn_clause(cls);
    justification js = m_solver->get_justification(l);
    justification njs(js.level());
    switch (cls.size()) {
        case 1:
            njs = justification(0, l);
            break;
        case 2:
            njs = justification(njs.level(), ~cls[1]);
            break;
        default:
            njs = justification(njs.level(), m_solver->get_offset(*c));
            break;
    }
    m_solver->update_assign_uncond(l, njs);
}

/*
** ---- END ---- Methods for clause learning
 */

/*
** ---- BEGIN ---- Methods for conflict analysis
 */

// get antecedents for literal put on trail by external solver
void sms_solver::get_antecedents(literal l, ext_justification_idx idx,
                                 literal_vector &r, bool probing) {
    if (l == null_literal) {
      if (probing) return;
      SASSERT(idx == PSOLVER_EXT_IDX);
      literal_vector cls;
      cls.push_back(l); 
      if (m_drating) drat_dump_cp(cls, idx);
      return;
    }
    sms_solver* s = idx == NSOLVER_EXT_IDX ? m_nSolver : m_pSolver;
    bool res = s->get_ext_reason(l, r);
    // when probing is true, sat solver is not doing conflict resolution
    if (probing) return;
    if (!res) {
        if (m_nSolver) m_nSolver->set_next_lit(l);
        else m_next_lit = l;
        set_unresolvable();
        return;
    }
    learn_clause_and_update_justification(l, r, idx);
}

// get reason for l when solver is not in a conflicting state
// returns false if l is caused by a decision
bool sms_solver::get_ext_reason(literal l, literal_vector &rc) {
    SASSERT(m_shared[l.var()]);
    literal_vector todo;
    literal t = l;
    todo.push_back(t);
    rc.reset();
    int_hashtable<int_hash, default_eq<int>> mark;
    while (!todo.empty()) {
        t = todo.back();
        todo.pop_back();
        if (mark.contains(t.var())) continue;
        mark.insert(t.var());
        dbg_print_lit("Fetching reason for", t);
        justification js = m_solver->get_justification(t);
        TRACE("satmodsat", m_solver->display_justification(tout, js););
        switch (js.get_kind()) {
            case justification::NONE: {
                if (js.level() != 0) {
                    // Decision variables involved in the conflict, exit without any justification
                    // SASSERT(m_finished_lookahead);
                    rc.reset();
                    return false;
                }
                break;
            }
            case justification::BINARY: {
                todo.push_back(~js.get_literal());
                break;
            }
            case justification::CLAUSE: {
                clause &c = m_solver->get_clause(js);
                unsigned i = 0;
                if (c[0].var() == t.var()) {
                    i = 1;
                } else {
                    SASSERT(c[1].var() == t.var());
                    todo.push_back(~c[0]);
                    i = 2;
                }
                unsigned sz = c.size();
                for (; i < sz; i++) { todo.push_back(~c[i]); }
                break;
            }
            case justification::EXT_JUSTIFICATION: {
                SASSERT(l.var() != t.var());
                rc.push_back(t);
                break;
            }
            default: {
                UNREACHABLE();
                break;
            }
        }
    }
    return true;
}


// Assume that s is unsat with unsat core m_ext_clause
// Learn clause m_ext_clause and set it as the conflict clause
// and set it as clause that is false under current trail
void sms_solver::set_conflict(sms_solver* s) {
    SASSERT(s != this);
    ext_justification_idx idx = s->get_ext_justification_idx();
    unsigned bjlvl = place_highest_dl_at_start(*m_ext_clause);
    pop_no_reinit(m_solver->scope_lvl() - bjlvl);
    if(m_ext_clause->size() > 0) {
        s->validate(*m_ext_clause);
        dbg_print_lv("other solver unsat with current trail, learning lemma ", *m_ext_clause);
    }
    else dbg_print("other solver unsat");
    if (m_drating) drat_dump_cp(*m_ext_clause, idx);
    clause *c = learn_clause(*m_ext_clause);
    // learning clauses cause propagation and conflict
    if (m_solver->inconsistent()) return;
    unsigned lvl = m_solver->lvl(m_ext_clause->get(0));
    justification js(lvl);
    // force conflict
    switch (m_ext_clause->size()) {
    case 0:
        //special case when one solver is unsat, learning it already made solver
        //inconsistent
        UNREACHABLE();
    case 1:
        // if its a unit clause, it cannot be simplified further, so no need for
        //conflict analysis
        SASSERT(m_solver->scope_lvl() == 0);
        break;
    case 2:
        js = justification(lvl, m_ext_clause->get(0));
        m_solver->set_conflict(js, ~m_ext_clause->get(1));
        break;
    default:
        clause_offset co = m_solver->get_offset(*c);
        js = justification(lvl, co);
        m_solver->set_conflict(js);
        break;
    }
    dbg_print_stat("conflict level", lvl);
}

/*
** ---- END ---- Methods for conflict analysis
 */

/*
** ---- BEGIN ---- Methods for inter-modular propagation
 */

// do inter modular propagation before search starts
void sms_solver::init_search() { unit_propagate(); }

bool sms_solver::unit_propagate() {
    if (get_mode() != SEARCH) return true;
    sms_solver* p = m_pSolver ? m_pSolver : m_nSolver;
    bool res =  p->propagate(this);
    if (!res) {
        if (p->unresolvable()) set_unresolvable();
        else set_conflict(p);
    }
    //the sat solver doesn't use the return value, return anything
    return true;
}

// propagate called by s
bool sms_solver::propagate(sms_solver* s) {
    SASSERT(get_mode() != SEARCH);
    // all shared variables are already on the trail.
    // update m_solver->m_qhead
    if (m_solver->propagate(false)) return true;
    dbg_print("getting final ext reason for conflict");
    if (m_solver->resolve_conflict_for_ext_core()) {
        dbg_print_lv("final reason is", *m_solver->get_ext_core());
        validate(*m_solver->get_ext_core());
        return false;
    }
    dbg_print("cannot express conflict in terms of shared vars");
    //Happens only during speculation
    SASSERT(!m_nSolver);
    SASSERT(get_mode() == PROPAGATE);
    SASSERT(s->get_mode() == SEARCH);
    SASSERT(m_solver->get_ext_core()->size() == 1);
    m_next_lit = m_solver->get_ext_core()->get(0);
    return false;
}

void sms_solver::asserted(literal l) {
    if (m_solver->lvl(l) == 0) {
        literal_vector uc; uc.push_back(l);
        validate(uc);
    }
    // synchronize assignments on shared variables
    if (m_shared[l.var()]) {
        sms_solver* s = m_pSolver ? m_pSolver : m_nSolver;
        s->assign_from_other(l, this);
    }
}

void sms_solver::assign_from_other(literal l, sms_solver* solver) {
    SASSERT(this != solver);
    lbool v = m_solver->value(l);
    //Solvers cannot disagree on assignments to shared variables
    SASSERT(v != l_false);
    if (v == l_undef) {
        justification js =
            justification::mk_ext_justification(solver->get_lit_lvl(l), solver->get_id());
        dbg_print_lit("assigning from other", l);
        m_solver->assign(l, js);
        if (m_solver->scope_lvl() == 0) {
            //the solver might change justifications at level 0
            m_solver->update_assign_uncond(l, js);
        }
    }
    return;
}

/*
** ---- END ---- Methods for inter-modular propagation
 */

/*
** ---- BEGIN ---- Methods for making decisions
 */

bool sms_solver::pick_random_unassigned(bool_var &next, lbool &phase) {
    unsigned sz =  m_preferred.size();
    unsigned i = sz;
    for (unsigned j = 0; j < i; j++) m_picked[j] = false;
    while(i > 0) {
        bool_var v = m_solver->rand()() % sz;
        if (m_picked[v]) continue;
        m_picked[v] = true;
        i--;
        if (m_solver->value(v) == l_undef) {
            next = v;
            phase = l_undef;
            return true;
        }
    }
    return false;
}

bool sms_solver::get_case_split(bool_var &next, lbool &phase) {
    if (!m_pSolver && get_mode() == SEARCH)
        return pick_random_unassigned(next, phase);
    return false;
}

bool sms_solver::decide(bool_var &next, lbool &phase) {
    SASSERT(get_mode() == SEARCH);
    if (m_next_lit != null_literal) {
        SASSERT(m_pSolver && m_pSolver->get_mode() == PROPAGATE);
        next = m_next_lit.var();
        SASSERT(m_solver->value(next) == l_undef);
        phase = m_next_lit.sign() ? l_true : l_false;
        m_next_lit = null_literal;
        return true;
    }
    // assign preferred vars
    if (pick_random_unassigned(next, phase)) return true;
    //never enter speculative execution
    if (m_lam_switch == 0 || !m_pSolver) return false;
    //all preferred variables have been picked, speculate
    SASSERT(m_solver->scope_lvl() > 0);
    unsigned search_lvl = m_solver->scope_lvl() - 1;
    dbg_print_stat("start SPECULATIVE execution", search_lvl);
    set_prop_mode();
    set_spec_lvl(search_lvl);
    m_pSolver->set_spec_lvl(search_lvl);
    lbool r = m_pSolver->modular_solve(search_lvl);
    switch (r) {
        case l_true: {
            // continue making decisions
            m_pSolver->set_fin_mode();
            SASSERT(m_pSolver->get_scope_lvl() == m_solver->scope_lvl());
            //now treat all decisions below m_solver->scope_lvl() as assumptions
            set_search_mode(m_solver->scope_lvl());
            dbg_print("SPECULATIVE execution return SAT, VALIDATING");
            m_solver->push();
            if (m_solver->value(next) == l_undef) return false;
            next = m_solver->next_var();
            phase = m_solver->guess(next) ? l_true : l_false;
            return true;
        }
        case l_false: {
            m_pSolver->set_prop_mode();
            set_search_mode(0);
            set_spec_lvl(0);
            //pSolver unsat with current decisions, learn lemma
            set_conflict(m_pSolver);
            return false;
        }
        case l_undef: {
            m_pSolver->set_prop_mode();
            set_search_mode(0);
            set_spec_lvl(0);
            literal l = m_next_lit;
            SASSERT(l != null_literal);
            m_next_lit = null_literal;
            pop_no_reinit(m_solver->scope_lvl() - m_solver->lvl(l));
            next = l.var();
            phase = l.sign() ? l_true : l_false;
            SASSERT(m_solver->value(next) == l_undef);
            return true;
        }
        default: UNREACHABLE();
    }
    UNREACHABLE();
}


check_result sms_solver::check() {
    if (!m_pSolver || m_pSolver->get_mode() == FINISHED) return check_result::CR_DONE;
    SASSERT(get_mode() == SEARCH);
    SASSERT(m_pSolver->get_mode() == PROPAGATE);
    unsigned full_assign_lvl = m_solver->scope_lvl();
    m_pSolver->set_search_mode(full_assign_lvl);
    set_fin_mode();
    dbg_print("got a sat assignment, checking with psolver");
    lbool res = m_pSolver->modular_solve(full_assign_lvl);
    SASSERT(res != l_undef);
    if (res == l_true) {
        m_pSolver->set_fin_mode();
        return check_result::CR_DONE;
    }
    m_pSolver->set_prop_mode();
    set_search_mode(0);
    //pSolver unsat with current decisions
    set_conflict(m_pSolver);
    SASSERT(m_solver->scope_lvl() < full_assign_lvl);
    return check_result::CR_CONTINUE;
}

bool sms_solver::switch_to_lam() {
    return m_lam_switch > 0;
}

/*
** ---- END ---- Methods for making decisions
 */

/*
** ---- BEGIN ---- Methods for synchronizing decision levels
 */

void sms_solver::push_from_other() { m_solver->push(); }

void sms_solver::push() {
    if (get_mode() != SEARCH) return;
    // Synchoronize decision levels between solvers
    if (m_pSolver) m_pSolver->push_from_other();
    if (m_nSolver) m_nSolver->push_from_other();
}

void sms_solver::pop_from_other(unsigned num_scopes) {
    m_solver->pop(num_scopes);
}

void sms_solver::pop(unsigned num_scopes) {
    dbg_print_stat("popping", num_scopes);
    unsigned bj_lvl = m_solver->scope_lvl() - num_scopes;
    if (!m_exiting &&  bj_lvl < m_search_lvl) {
        dbg_print("backjumping below search lvl, will trigger reinit");
        m_replay_assign.reset();
        m_replay_just.reset();
        m_solver->save_trail(bj_lvl, m_search_lvl, m_replay_assign, m_replay_just);
    }
    if (get_mode() != SEARCH) return;
    // Synchoronize decision levels between solvers
    if (m_pSolver) m_pSolver->pop_from_other(num_scopes);
    if (m_nSolver) m_nSolver->pop_from_other(num_scopes);
}

// add literals below level lvl in m_replay_assign to the trail
// use s to synchronize decision levels
void sms_solver::reinit_saved_trail(sms_solver* s, unsigned lvl = UINT32_MAX) {
    SASSERT(s->get_mode() == SEARCH);
    for(unsigned i = 0, sz = m_replay_assign.size(); i < sz; i++) {
        justification js = m_replay_just[i];
        literal l = m_replay_assign[i];
        if (js.level() < m_solver->scope_lvl()) {
            SASSERT(m_solver->value(l) != l_undef);
            continue;
        }
        if(js.level() > lvl) break;
        dbg_print_stat("re-initializing at lvl", js.level());
        SASSERT(m_solver->scope_lvl() == s->get_scope_lvl());
        while (m_solver->scope_lvl() < js.level()) s->push_from_other();
        // The trail is unordered. So we could be assigning literals at a
        // lower level than solver->scope_lvl()
        m_solver->assign(l, js);
        // synchronize trail manually since assign does not have a callback
        s->assign_from_other(l, this);
        SASSERT(!m_solver->inconsistent());
    }
}
void sms_solver::pop_reinit() {
    if (m_exiting) return;
    if(get_mode() != SEARCH) return;
    // Reinitialize all decisions made by this solver before it speculated
    // Happens only during validation
    if (m_pSolver && m_solver->scope_lvl() < m_spec_lvl) {
        SASSERT(m_pSolver->get_mode() == FINISHED);
        reinit_saved_trail(this, m_spec_lvl);
    }

    // Reinitialize all decisions in the other solver, when it was in SEARCH mode
    if (m_pSolver) m_pSolver->reinit_saved_trail(this, m_search_lvl);
    else m_nSolver->reinit_saved_trail(this, m_search_lvl);

    //reinit all decisions made in the current SEARCH mode
    reinit_saved_trail(this);
}

void sms_solver::pop_no_reinit(unsigned num_scopes) {
    m_exiting = true;
    m_solver->pop(num_scopes);
    m_exiting = false;
}

/*
** ---- END ---- Methods for synchronizing decision levels
 */


void sms_solver::process_antecedents_for_ext_unit(justification js, literal l, literal_vector& todo) {
    literal_vector rc;
    switch (js.get_kind()) {
        case justification::NONE:
            SASSERT(js.level() == 0);
            break;
        case justification::BINARY:
            SASSERT(m_solver->lvl(js.get_literal()) == 0);
            todo.push_back(js.get_literal());
            break;
        case justification::CLAUSE: {
            clause &c = m_solver->get_clause(js);
            unsigned i = 0;
            unsigned sz = c.size();
            for (i = 0; i < sz; i++) {
                SASSERT(m_solver->lvl(c[i]) == 0);
                if (c[i].var() != l.var()) todo.push_back(c[i]);
            }
            break;
        }
        case justification::EXT_JUSTIFICATION: {
            rc.reset();
            get_antecedents(~l, js.get_ext_justification_idx(), rc, false);
            unsigned i = 0;
            for (i = 0; i < rc.size(); i++) {
                SASSERT(m_solver->lvl(rc[i]) == 0);
                if (rc[i].var() != l.var()) todo.push_back(rc[i]);
            }
            break;
        }
        default:
            SASSERT(false);
        }
}

lbool sms_solver::resolve_conflict() {
    if (m_solver->at_base_lvl()) {
        resolve_all_ext_unit_lits();
    }
    return l_undef;
}

void sms_solver::resolve_all_ext_unit_lits() {
    literal_vector todo;
    literal l = m_solver->get_m_not_l();

    if (l != null_literal) {
        justification js = m_solver->get_conflict();
        process_antecedents_for_ext_unit(js,  l, todo);
    }
    todo.push_back(l);
    justification js(0);
    int_hashtable<int_hash, default_eq<int>> mark;
    while (!todo.empty()) {
        l = todo.back();
        todo.pop_back();
        if (mark.contains(l.var())) continue;
        mark.insert(l.var());
        if (l == null_literal) {
            js = m_solver->get_conflict();
            if (js.is_ext_justification()) continue;
        }
        else {
            js = m_solver->get_justification(l);
            SASSERT(m_solver->lvl(l) == 0);
        }
        process_antecedents_for_ext_unit(js,  l, todo);
    }
}


// MAIN METHOD

// all decisions below lvl are assumptions
// returns true (sat), false (hit a conflict below lvl), or
// undef (cannot resolve a conflict)
// if unsat/undef, sat solver is in inconsistent state. Backjumping is not done
// if unsat, m_core contains the ext assumptions that caused unsat
// if undef, m_next_lit is the literal to refine
lbool sms_solver::modular_solve(unsigned lvl) {
    set_search_mode(lvl);
    dbg_print_stat("reached modular solve with", lvl);
    lbool r = m_solver->search_above();
    //if modular solve returned unresolvable during validation, try again
    if (r == l_undef && m_pSolver && m_pSolver->get_mode() == FINISHED) {
        SASSERT(m_next_lit != null_literal);
        pop_no_reinit(m_solver->scope_lvl() - m_spec_lvl);
        set_spec_lvl(0);
        r = m_solver->search_above();
        SASSERT(r != l_undef);
    }
    dbg_print_stat("finished modular solve with", r);
    return r;
}

/*
 Functions to add clauses to solvers
 TODO: replace with standard way of doing it e.g. in euf_solver.h
 */
void sms_solver::add_clause_expr(expr *fml) {
    expr *n;
    SASSERT(m.is_or(fml) ||
            (m.is_bool(fml) && (is_uninterp_const(fml) ||
                                (m.is_not(fml, n) && is_uninterp_const(n)))));
    ptr_vector<expr> args;
    if (!m.is_or(fml)) {
        args.push_back(fml);
    } else
        for (expr *e : *to_app(fml)) args.push_back(e);
    literal_vector c;
    bool t;
    bool_var v;
    literal l;
    for (expr *e : args) {
        SASSERT(m.is_bool(e));
        n = e;
        t = m.is_not(e, n);
        SASSERT(is_uninterp_const(n));
        v = boolVar(n);
        l = literal(v, t);
        c.push_back(l);
    }
    m_solver->add_clause(c.size(), c.data(), sat::status::input());
    m_validator->add_clause(c.size(), c.data(), sat::status::input());
}

void satmodsatcontext::addA(expr_ref fml) {
    add_cnf_expr_to_solver(m_solverA, fml);
}

void satmodsatcontext::addB(expr_ref fml) {
    add_cnf_expr_to_solver(m_solverB, fml);
}

void satmodsatcontext::add_cnf_expr_to_solver(extension *s, expr_ref fml) {
    sms_solver *a = static_cast<sms_solver *>(s);
    SASSERT(m.is_and(fml));
    for (expr *e : *to_app(fml)) { a->add_clause_expr(e); }
}

bool sat_mod_sat::solve(expr_ref A, expr_ref B, expr_ref_vector &shared, expr_ref_vector &prefA, expr_ref_vector &prefB) {
    TRACE("satmodsat",
          tout << "A: " << mk_pp(A, m) << " B: " << mk_pp(B, m) << "\n";);
    init(A, B, shared, prefA, prefB);
    bool res = m_solver.solve();
    const char *s = res ? "satisfiable" : "unsatisfiable";
    TRACE("satmodsat", tout << "final result is " << s;);
    return res;
}

// Ensures that all shared variables have the same index in both solvers.
// That is variable 1 in Solver_A is the same as variable 1 in solver_B
// This is required to reduce the amount of bookkeeping when exchanging lits and
// clauses between solvers
void sat_mod_sat::init(expr_ref A, expr_ref B, expr_ref_vector const &shared, expr_ref_vector const &prefA, expr_ref_vector const &prefB) {
    m_a = A;
    m_b = B;
    m_shared = expr_ref_vector(shared);
    m_solver.addShared(shared);
    m_solver.addPreferred(prefA, prefB);
    m_solver.addA(m_a);
    m_solver.addB(m_b);
}
