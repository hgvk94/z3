#include "sat/sms/sms_solver.h"
#include "ast/ast_pp.h"
#include "sat/sat_justification.h"
#include "sat/sat_types.h"
#include "util/debug.h"
#include "util/lbool.h"
#include "util/sat_literal.h"
#include "sat/sms/sms_proof_itp.h"

using namespace sat;

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
    (*m_out) << "\n";
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

// place literal with highest dl in cls at position 0
// returns level at which cls is asserting
unsigned sms_solver::place_highest_dl_at_start(literal_vector& cls) {
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
    for (auto i = 1; i < cls.size(); i++) {
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

// learn clause (l || antecedent) from external solver idx
void sms_solver::learn_clause_and_update_justification(
    literal l, literal_vector const &antecedent, ext_justification_idx idx) {
    literal_vector cls;
    cls.push_back(l);
    for (auto a : antecedent) cls.push_back(a);
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

void sms_solver::get_antecedents(literal l, ext_justification_idx idx,
                                 literal_vector &r, bool probing) {
    if (l == null_literal) {
      SASSERT(idx == PSOLVER_EXT_IDX);
      if (probing) return;
      literal_vector cls;
      cls.push_back(l); 
      if (m_drating) drat_dump_cp(cls, idx);
      return;
    }
    if (idx == NSOLVER_EXT_IDX) {
        // Literal was asserted by nSolver
        // Right now, even when there is a conflcit below assumptions level, we attempt to resolve it
        SASSERT(probing || (m_nSolver && (m_nSolver->get_mode() == LOOKAHEAD || m_nSolver->get_mode() == FINISHED)));
        m_nSolver->get_ext_reason(l, r);
    } else {
        SASSERT(m_pSolver);
        // should have exited validate mode before conflict resolution
        bool res = m_pSolver->get_ext_reason(l, r);
        (void) res;
        SASSERT(probing || res);
    }
    // when probing is true, sat solver is not doing conflict resolution
    if (probing) return;
    learn_clause_and_update_justification(l, r, idx);
}

void sms_solver::init_search() { unit_propagate(); }

bool sms_solver::get_reason_final(literal_vector &lc,
                                  ext_justification_idx eidx) {
    dbg_print("getting final ext reason for conflict");
    if (m_solver->resolve_conflict_for_ext_core(lc, eidx)) {
        dbg_print_lv("final reason is", lc);
        validate(lc);
        return true;
    }
    dbg_print("cannot express conflict in terms of shared vars");
    lc.reset();
    return false;
}

bool sms_solver::unit_propagate() {
    if (get_mode() == FINISHED) return true;
    if (m_pSolver && get_mode() != LOOKAHEAD) {
        m_pSolver->reset_asserted();
        bool r = m_pSolver->propagate();
        if (!r) {
            SASSERT(get_mode() == SEARCH);
            m_ext_clause.reset();
            VERIFY(m_pSolver->get_reason_final(m_ext_clause, NSOLVER_EXT_IDX));
            set_conflict(m_pSolver);
            return false;
        }
        literal_vector const &t = m_pSolver->get_asserted();
        for (literal l : t) { assign_from_other(l, m_pSolver); }
    }
    if (m_nSolver && m_nSolver->get_mode() == LOOKAHEAD) {
        m_nSolver->reset_asserted();
        bool r = m_nSolver->propagate();
        if (!r) {
            m_ext_clause.reset();
            if (m_nSolver->get_reason_final(m_ext_clause, PSOLVER_EXT_IDX)) {
                set_conflict(m_nSolver);
            } else {
                exit_search(get_search_lvl());
            }
            return false;
        }
        literal_vector const &t = m_nSolver->get_asserted();
        for (literal l : t) { assign_from_other(l, m_nSolver); }
    }
    return true;
}

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
    SASSERT(get_mode() != PROPAGATE);
    //there is no psolver to speculate
    if (!m_pSolver || get_mode() != SEARCH) return false;
    // assign preferred vars
    if (pick_random_unassigned(next, phase)) return true;
    //never enter speculative execution
    if (m_lam_switch == 0) return false;
    //all preferred variables have been picked, speculate
    m_solver->push();
    dbg_print("switching to LOOKAHEAD MODE");
    unsigned search_lvl = m_solver->scope_lvl();
    m_pSolver->set_search_mode(search_lvl);
    set_mode(LOOKAHEAD);
    m_pSolver->set_core(m_ext_clause);
    bool r = m_pSolver->modular_solve();
    if (r) {
        // continue making decisions
        m_pSolver->set_mode(FINISHED);
        SASSERT(m_pSolver->get_scope_lvl() == m_solver->scope_lvl());
        set_validate_mode(search_lvl, m_solver->scope_lvl());
        dbg_print("LOOKAHEAD return SAT, VALIDATING");
        m_solver->push();
        if (m_solver->value(next) == l_undef) return false;
        next = m_solver->next_var();
        phase = m_solver->guess(next) ? l_true : l_false;
        return true;
    }
    //m_pSolver refined
    if (m_pSolver->get_next_decision() != null_literal) {
        m_pSolver->set_mode(PROPAGATE);
        set_search_mode(0);
        next = m_pSolver->get_next_decision().var();
        phase = m_pSolver->get_next_decision().sign() ? l_true : l_false;
        SASSERT(m_solver->value(next) == l_undef);
        m_pSolver->set_next_decision(null_literal);
        return true;
    }
    m_pSolver->set_mode(PROPAGATE);
    //pSolver unsat with current decisions, learn lemma
    set_conflict(m_pSolver);
    SASSERT(get_mode() == SEARCH);
    return false;
}

// Assume that solver is unsat with unsat core m_ext_clause
// Learn clause m_ext_clause and set it as the conflict clause
// and set it as clause that is false under current trail
void sms_solver::set_conflict(sms_solver* solver) {
    SASSERT(solver != this);
    ext_justification_idx idx = solver->get_ext_justification_idx();
    // solver is unsat by itself
    if (solver->is_unsat() || m_ext_clause.empty()) {
        dbg_print("other solver unsat");
        SASSERT(!m_solver->inconsistent());
        SASSERT(m_solver->scope_lvl() == 0);
        m_unsat = true;
        justification js = justification::mk_ext_justification(0, idx);
        m_solver->set_conflict(js, null_literal);
        return;
    }

    // solver is unsat with decisions in this
    // learn m_ext_clause
    SASSERT(!m_ext_clause.empty());
    place_highest_dl_at_start(m_ext_clause);
    solver->validate(m_ext_clause);
    dbg_print_lv("other solver unsat with current trail, learning lemma ", m_ext_clause);
    if (m_drating) drat_dump_cp(m_ext_clause, idx);
    clause *c = learn_clause(m_ext_clause);
    // learning binary clauses cause propagation and conflict
    if (m_solver->inconsistent()) return;
    unsigned lvl = m_solver->lvl(m_ext_clause[0]);
    justification js(lvl);
    // force conflict
    switch (m_ext_clause.size()) {
    case 1:
        // if its a unit clause, it cannot be simplified further, so no need for
        //conflict analysis
        SASSERT(m_solver->scope_lvl() == 0);
        break;
    case 2:
        js = justification(lvl, m_ext_clause[0]);
        m_solver->set_conflict(js, ~m_ext_clause[1]);
        break;
    default:
        clause_offset co = m_solver->get_offset(*c);
        js = justification(lvl, co);
        m_solver->set_conflict(js);
        break;
    }
    dbg_print_stat("conflict level", lvl);
}

void sms_solver::asserted(literal l) {
    dbg_print_lit("asserted lit", l);
    TRACE("satmodsat", m_solver->display_justification(tout, m_solver->get_justification(l)););
    if (m_solver->lvl(l) == 0) {
        literal_vector uc; uc.push_back(l);
        validate(uc);
    }
    if (m_shared[l.var()]) {
        m_asserted.push_back(l);
        if (m_pSolver && get_mode() != LOOKAHEAD)
            m_pSolver->assign_from_other(l, this);
        if (m_nSolver && m_nSolver->get_mode() == LOOKAHEAD)
            m_nSolver->assign_from_other(l, this);
    }
}

void sms_solver::assign_from_other(literal l, sms_solver* solver) {
    SASSERT(this != solver);
    justification js =
        justification::mk_ext_justification(solver->get_lit_lvl(l), solver->get_id());
    switch (m_solver->value(l)) {
    case l_undef:
        dbg_print_lit("assigning from other", l);
        m_solver->assign(l, js);
        if (m_solver->scope_lvl() == 0) {
            //the solver might change justifications at level 0
            m_solver->update_assign_uncond(l, js);
        }
        break;
    case l_true:
        return;
    case l_false:
        m_solver->set_conflict(js, ~l);
    }
}

// get reason for l when solver is not in a conflicting state
// returns false if l is caused by a decision
bool sms_solver::get_ext_reason(literal l, literal_vector &rc) {
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
                rc.push_back(~t);
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

void sms_solver::push_from_other() { m_solver->push(); }

void sms_solver::push() {
    // Synchoronize decision levels between solvers
    if (m_pSolver && get_mode() != LOOKAHEAD &&  get_mode() != FINISHED)
        m_pSolver->push_from_other();
    if (m_nSolver && (m_nSolver->get_mode() == LOOKAHEAD ||
                      m_nSolver->get_mode() == FINISHED))
        m_nSolver->push_from_other();
}

void sms_solver::pop_from_other(unsigned num_scopes) {
    m_solver->pop(num_scopes);
}

void sms_solver::exit_search(unsigned lvl) {
    SASSERT(get_mode() == SEARCH);
    SASSERT(m_nSolver && (m_nSolver->get_mode() == LOOKAHEAD ||
                          m_nSolver->get_mode() == FINISHED));
    SASSERT(lvl <= get_search_lvl());
    dbg_print_stat("exiting search mode", lvl);
    m_exiting = true;
    m_solver->pop(m_solver->scope_lvl() - lvl);
    set_mode(PROPAGATE);
    m_nSolver->set_search_mode(0);
    m_exiting = false;
}


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

void sms_solver::exit_unsat() {
  dbg_print("unsat");
  m_unsat = true;
  //learn all ext prop at lvl 0
  resolve_all_ext_unit_lits();
  if (m_nSolver && m_nSolver->get_mode() == LOOKAHEAD) {
    m_exiting = true;
    m_solver->pop(m_solver->scope_lvl());
    set_mode(PROPAGATE);
    m_nSolver->set_mode(SEARCH);
    m_exiting = false;
    return;
  }
  m_solver->pop(m_solver->scope_lvl());
  return;
}

void sms_solver::exit_validate(unsigned lvl) {
    SASSERT(m_pSolver && m_pSolver->get_mode() == FINISHED &&
            get_mode() == VALIDATE);
    SASSERT(lvl <= get_validate_lvl());
    lvl = lvl <= get_search_lvl() ? lvl : get_search_lvl();
    dbg_print_stat("exiting validate mode, jumping to ", lvl);
    m_exiting = true;
    m_solver->pop(m_solver->scope_lvl() - lvl);
    set_mode(SEARCH);
    m_pSolver->set_mode(PROPAGATE);
    m_exiting = false;
}

void sms_solver::find_and_set_decision_lit() {
    SASSERT(m_solver->inconsistent());
    literal l;
    literal_vector todo;
    justification js(0);
    todo.push_back(m_solver->get_m_not_l());
    while (!todo.empty()) {
        l = todo.back();
        todo.pop_back();
        js = m_solver->get_justification(l);
        if (m_shared[l.var()]) {
            set_next_decision(l);
            return;
        }
        switch (js.get_kind()) {
        case justification::NONE:
            SASSERT(false);
            break;
        case justification::BINARY:
            todo.push_back(js.get_literal());
            break;
        case justification::CLAUSE: {
            clause &c = m_solver->get_clause(js);
            unsigned i = 0;
            unsigned sz = c.size();
            for (i = 0; i < sz; i++) todo.push_back(c[i]);
            break;
        }
        default:
            SASSERT(false);
        }
    }
    SASSERT(false);
}

void sms_solver::handle_mode_transition() {
  if (get_mode() == VALIDATE) {
      if (get_reason_final(m_ext_clause, PSOLVER_EXT_IDX)) {
          unsigned bj_lvl = place_highest_dl_at_start(m_ext_clause);
          exit_validate(bj_lvl);
          dbg_print_lv("validate hit a conflict below validate lvl, learning "
                       "lemma and exiting", m_ext_clause);
          validate(m_ext_clause);
          learn_clause(m_ext_clause);
      } else {
          find_and_set_decision_lit();
          exit_validate(get_search_lvl());
          dbg_print_lit("validate hit a conflict below validate lvl, exiting "
                        "with new decision",
                        m_next_lit);
      }
  }
  else {
    SASSERT(get_mode() == SEARCH);
    SASSERT(m_nSolver);
    if(get_reason_final(*m_core, NSOLVER_EXT_IDX)) {
        dbg_print_lv("search hit a conflict below search lvl, learning lemma "
                     "and exiting", *m_core);
        SASSERT(m_core != nullptr);
        unsigned bj_lvl = place_highest_dl_at_start(*m_core);
        exit_search(bj_lvl);
        validate(m_ext_clause);
        // learn clause in psolver as well. This is optional
        learn_clause(*m_core);
    }
    else {
        find_and_set_decision_lit();
        exit_search(get_search_lvl());
        dbg_print_lit("search hit an unrecoverable conflict "
                      "with new decision",
                        m_next_lit);
    }
  }
}

// resolve_conflict checks whether the current conflict can be
// resolved in the current solver.
// if conflict can be resolved, it returns l_undef so that the sat solver can
// resolve the conflict
// if conflict requires the solver to jump to a different mode, it handles lemma learning and backjumping
lbool sms_solver::resolve_conflict() {
    SASSERT(get_mode() == SEARCH || get_mode() == VALIDATE);
    SASSERT(!m_nSolver || m_nSolver->get_mode() == FINISHED || m_nSolver->get_mode() == LOOKAHEAD);
    unsigned c_lvl = m_solver->compute_conflict_lvl();

    //Case 1. Solver UNSAT
    if (c_lvl == 0) {
        exit_unsat();
        return l_false;
    }

    // Case 2. This conflict forces solver mode transition immediately
    // i.e. conflict level is below validate/search level
    // handle backjumping, make solver transitions and return false
    if (c_lvl <= (get_mode() == VALIDATE ? get_validate_lvl() : get_search_lvl())) {
       handle_mode_transition();
       return l_false;
    }

    unsigned  bj_lvl = 0;
    literal_vector lemma;
    literal_vector unit_lits;
    bool resolvable = m_solver->check_resolvable(c_lvl, bj_lvl, lemma, unit_lits);

    // Case 3. Conflict cannot be resolved in one module. refine
    if (!resolvable) {
        handle_mode_transition();
        return l_false;
    }

    // Case 4. Conflict might cause backjumping to level below validate/search
    // but no immediate mode transition
    if ((get_mode() == VALIDATE && bj_lvl < m_validate_lvl) ||
         (get_mode() == SEARCH && bj_lvl < m_search_lvl)) {
        unsigned end_of_saved_trail = get_mode() == VALIDATE ? m_validate_lvl : m_search_lvl;
        //save trail
        m_replay_assign.reset();
        m_replay_just.reset();
        m_solver->save_trail(bj_lvl, end_of_saved_trail, m_replay_assign, m_replay_just);
        dbg_print_lv("to reinit", m_replay_assign);
        m_solver->pop(m_solver->scope_lvl() - bj_lvl);
        SASSERT(m_solver->scope_lvl() == bj_lvl);
        SASSERT(!m_solver->inconsistent());
        validate(lemma);
        learn_clause(lemma);
        ext_justification_idx idx = get_mode() == VALIDATE ? PSOLVER_EXT_IDX : NSOLVER_EXT_IDX;
        for(literal l : unit_lits) {
            literal_vector uc(1, {l});
            if (m_drating) drat_dump_cp(uc, idx);
            sms_solver* s = get_mode() == VALIDATE ? m_pSolver : m_nSolver;
            s->validate(uc);
            learn_clause(uc);
        }
        auto handle_reinit_conflict = [&] () {
            dbg_print_stat("reinit hit a conflict at level", m_solver->scope_lvl());
            SASSERT(m_solver->inconsistent());
            if (m_solver->scope_lvl() == 0) exit_unsat();
            else handle_mode_transition();
            return l_false;
        };
        //reinit assumptions
        m_solver->propagate(false);
        if (m_solver->inconsistent()) {
            return handle_reinit_conflict();
        }

        while (m_solver->scope_lvl() < end_of_saved_trail) m_solver->push();
        if (m_replay_assign.empty()) return l_false;
        dbg_print_lv("reinitializing", m_replay_assign);
        for(unsigned i = 0, sz = m_replay_assign.size(); i < sz; i++) {
            justification js = m_replay_just[i];
            literal l = m_replay_assign[i];
            SASSERT(m_solver->scope_lvl() <= js.level());
            while (m_solver->scope_lvl() < js.level()) m_solver->push();
            // The trail is unordered. So we could be assigning literals at a
            // lower level than solver->scope_lvl()
            SASSERT(js.level() >= bj_lvl);
            m_solver->assign(l, js);
            m_solver->propagate(false);
            if (m_solver->inconsistent()) {
                return handle_reinit_conflict();
            }
        }
        // reinit did not hit a conflict, continue making decisions
        return l_false;
    }
    return l_undef;
}

void sms_solver::pop_reinit() { }

void sms_solver::pop(unsigned num_scopes) {
    dbg_print_stat("popping", num_scopes);
    if (m_pSolver && get_mode() != LOOKAHEAD && get_mode() != FINISHED)
        m_pSolver->pop_from_other(num_scopes);
    if (get_mode() == SEARCH && m_nSolver)
        m_nSolver->pop_from_other(num_scopes);
}

bool sms_solver::propagate() { return m_solver->propagate(false); }

check_result sms_solver::check() {
    if (!m_pSolver || get_mode() == VALIDATE) return check_result::CR_DONE;
    SASSERT(get_mode() == SEARCH);
    SASSERT(m_pSolver->get_mode() == PROPAGATE);
    unsigned search_lvl = m_solver->scope_lvl();
    m_pSolver->set_search_mode(search_lvl);
    set_mode(FINISHED);
    dbg_print("got a sat assignment, checking with psolver");
    m_pSolver->set_core(m_ext_clause);
    if (m_pSolver->modular_solve()) {
        m_pSolver->set_mode(FINISHED);
        return check_result::CR_DONE;
    }
    //pSolver unsat with current decisions
    set_conflict(m_pSolver);
    SASSERT(get_mode() == SEARCH);
    return check_result::CR_CONTINUE;
}

bool sms_solver::switch_to_lam() {
    return m_lam_switch > 0;
}

bool sms_solver::modular_solve() {
    m_full_assignment_lvl = m_solver->scope_lvl();
    dbg_print_stat("reached modular solve with", m_full_assignment_lvl);
    bool r = m_solver->search_above(m_full_assignment_lvl);
    dbg_print_stat("finished modular solve with", m_solver->scope_lvl());
    // The following assertion does not hold because solver does not backjump
    // when conflict lvl is 0
    //  SASSERT(r || m_solver->scope_lvl() <= m_full_assignment_lvl);
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
