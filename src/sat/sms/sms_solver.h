#pragma once
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "sat/sat_clause.h"
#include "sat/sat_extension.h"
#include "sat/sat_solver.h"
#include "sat/sat_types.h"
#include "util/debug.h"
#include "util/lbool.h"
#include "util/memory_manager.h"
#include "util/params.h"
#include "util/sat_literal.h"
#include "util/symbol.h"
#include "util/vector.h"
#include "sat/sms/sms_validator.h"

namespace sat {

#define dbg_print(s)                                                    \
    {                                                                   \
        TRACE("satmodsat",                                              \
              tout << "solver" << m_name << " " << m_mode << " "        \
              << m_spec_lvl << " " << m_search_lvl << " " << m_solver->scope_lvl() << " " << s;);   \
    }

#define dbg_print_stat(s, t)                                            \
    {                                                                   \
        TRACE("satmodsat", tout << "solver" << m_name << " "            \
              << m_mode << " " << m_spec_lvl << " " <<                \
              m_search_lvl << " " << m_solver->scope_lvl() << " " << s << " " << t;);                 \
    }

#define dbg_print_lit(s, l, u)                                          \
    {                                                                   \
        TRACE("satmodsat",tout << "solver" << m_name << " "             \
              << m_mode << " " << m_spec_lvl << " "                     \
              << m_search_lvl << " " << m_solver->scope_lvl() << " " << s;                            \
            if (l.sign()) {                                             \
                tout << " -" << expr_ref(get_expr(l.var()), m);         \
            } else {                                                    \
                tout << " " << expr_ref(get_expr(l.var()), m);          \
            } tout << " " << u;);                                       \
    }

#define dbg_print_lv(s, lv) {                                           \
    TRACE("satmodsat", tout << "solver" << m_name << " " << m_mode      \
          << " " << m_spec_lvl << " " << m_search_lvl << " " << m_solver->scope_lvl()              \
          << " " << s;                                                  \
          for (literal l : lv) {                                        \
              if (l.sign()) {                                           \
                  tout << " -" << expr_ref(get_expr(l.var()), m);       \
              } else {                                                  \
                  tout << " " << expr_ref(get_expr(l.var()), m);        \
              }                                                         \
          };);                                                          \
    }

#define NSOLVER_EXT_IDX 2
#define PSOLVER_EXT_IDX 1
#define UNDEF_EXT_IDX 2

enum sms_mode { FINISHED, PROPAGATE, SEARCH };

inline std::ostream &operator<<(std::ostream &out, const sms_mode m) {
    switch (m) {
    case PROPAGATE:
        return out << "PROPAGATE MODE";
    case SEARCH:
        return out << "SEARCH MODE";
    case FINISHED:
        return out << "FINISHED MODE";
    default:
        break;
    }
    UNREACHABLE();
    return out;
}
class sms_proof_itp;
class sms_solver : public extension {
    ast_manager &m;
    obj_map<expr, unsigned> m_expr2var;
    expr_ref_vector m_var2expr;
    bool_vector m_shared;
    svector<unsigned> m_preferred;
    literal_vector* m_ext_clause;
    sms_solver *m_pSolver;
    sms_solver *m_nSolver;
    sms_validator* m_validator;
    // Keep track of how many times literals have been exchanged.
    // Might be useful for conflict analysis
    size_t m_tx_idx;
    bool m_construct_itp;
    sms_mode m_mode;
    bool m_exiting;
    unsigned m_search_lvl, m_spec_lvl;
    svector<justification> m_replay_just;
    literal m_next_lit;
    bool m_unsat;
    bool_vector m_picked;
    literal_vector m_replay_assign;
    std::ostream* m_out;
    sms_proof_itp* m_itp;
    bool m_made_shared_assignment;

    // if m_lam_switch is 0, we never speculate
    unsigned m_lam_switch;
    bool_var addVar(expr *n) {
        expr_ref e(n, m);
        unsigned v;
        SASSERT(!m_expr2var.find(n, v));
        v = m_solver->add_var(true);
        m_validator->add_var(get_id());
        TRACE("satmodsat",
              tout << "adding var " << v << " for expr " << expr_ref(n, m););
        m_expr2var.insert(n, v);
        if (m_var2expr.size() <= v) { m_var2expr.resize(v + 1); }
        m_var2expr[v] = e;
        if (m_shared.size() <= v) m_shared.resize(v + 1);
        m_shared[v] = false;
        return v;
    }
    bool_var boolVar(expr *n) {
        unsigned v = 0;
        if (m_expr2var.find(n, v)) return v;
        return addVar(n);
    }
    void exit_validate(unsigned lvl);
    void exit_search(unsigned lvl);
    void exit_unsat();
    void find_and_set_decision_lit();
    void update_params(params_ref const & p) {
        m_lam_switch = p.get_uint("lam_switch", 1);
    }
    //exit speculation
    bool exit_speculation(literal& l);
  public:
    sms_solver(ast_manager &am, symbol const &name, int id, const params_ref p)
        : extension(name, id), m(am), m_var2expr(m),
          m_pSolver(nullptr), m_nSolver(nullptr), m_tx_idx(0),
          m_construct_itp(false),
          m_mode(SEARCH), m_exiting(false), m_search_lvl(0), m_spec_lvl(0),
          m_next_lit(null_literal), m_unsat(false), m_itp(nullptr) {
        update_params(p);
        m_ext_clause = alloc(literal_vector);
    }
    ~sms_solver() {
      m_out->flush();
      dealloc(m_ext_clause);
    }
        ext_justification_idx get_ext_justification_idx() const { return m_id; }
    void drat_dump_ext_unit(literal, ext_justification_idx);
    void init_drat(std::ostream* s) {
        m_drating = true;
        m_out = s;
    }

    bool is_in_ext_core(bool_var v) override { return m_shared[v]; }
    void dump(unsigned sz, literal const* lc, status st) override;
    void dump_clause(unsigned sz, literal const* lc);
    void drat_dump_cp(literal_vector const&, ext_justification_idx);    
    bool is_unsat() const { return m_solver->at_base_lvl(); }
    bool unresolvable() const { return m_solver->unresolvable(); }
    void set_unresolvable() { m_solver->set_unresolvable(); }
    void reset_unresolvable() { m_solver->reset_unresolvable(); }

    void set_next_lit(literal l) { dbg_print_stat("refining on lit ", l) m_next_lit = l; }
    void reset_next_decision() { m_next_lit = null_literal; }
    unsigned get_search_lvl() const { return m_search_lvl; }
    unsigned get_scope_lvl() const { return m_solver->scope_lvl(); }
    void reinit_decision(sms_solver* s, unsigned lvl);

    // all decisions before lvl are treated as assumptions
    void set_search_mode(unsigned lvl) {
        m_mode = SEARCH;
        m_search_lvl = lvl;
        m_solver->set_ext_assumption_lvl(lvl);
        m_made_shared_assignment = false;
    }

    void save_trail(unsigned start, unsigned end);
    // when refining, solver backjumps to m_spec_lvl
    void set_spec_lvl(unsigned lvl) {
        m_spec_lvl = lvl;
    }

    sms_mode get_mode() { return m_mode; }
    void set_prop_mode() { m_mode = PROPAGATE; m_search_lvl = 0; m_made_shared_assignment = false; }
    void set_fin_mode() { m_mode = FINISHED; m_search_lvl = 0; m_made_shared_assignment = false; }
    void learn_ext_core(sms_solver* solver);
    void handle_mode_transition();
    // void pop_reinit() override;
    void construct_itp() { m_construct_itp = true; }
    void set_pSolver(sms_solver *p) { m_pSolver = p; p->set_core(m_ext_clause); }
    void set_nSolver(sms_solver *n) { m_nSolver = n; n->set_core(m_ext_clause); }
    bool get_ext_reason(literal, literal_vector &);
    bool get_reason_final(literal_vector &, ext_justification_idx);
    void get_antecedents(literal, ext_justification_idx, literal_vector &,
                         bool) override;
    void
    learn_clause_and_update_justification(literal l,
                                          literal_vector const &antecedent, ext_justification_idx id);
    bool decide(bool_var &, lbool &) override;
    unsigned place_highest_dl_at_start(literal_vector& cls,  bool& unique_max);
    clause* learn_clause(literal_vector& cls, bool is_asserting = false);
    bool unit_propagate() override;
    void asserted(literal) override;
    unsigned get_lit_lvl(literal l) {
        SASSERT(m_solver->value(l) != l_undef);
        return m_solver->get_justification(l.var()).level();
    }
    void assign_from_other(literal, sms_solver*);
    void push_from_other();
    void init_search() override;
    void push() override;
    void pop(unsigned) override;
    void pop_from_other(unsigned);
    void pop_no_reinit(unsigned);
    void pop_reinit() override;
    bool propagate(sms_solver*);
    void set_core(literal_vector *c) { m_solver->set_ext_core(c); }
    bool switch_to_lam();
    std::ostream &display(std::ostream &out) const override {
        return out << "display yet to be implemented\n";
    }

    std::ostream &
    display_justification(std::ostream &out,
                          ext_justification_idx idx) const override {
        switch (idx) {
        case NSOLVER_EXT_IDX:
            return out << "literal from NSOLVER";
        case PSOLVER_EXT_IDX:
            return out << "literal from PSOLVER";
        default:
            UNREACHABLE();
            return out;
        }
    }

    std::ostream &display_constraint(std::ostream &out,
                                     ext_constraint_idx idx) const override {
        return out << "display constraint yet to be implemented " << idx
                   << "\n";
    }

    check_result check() override;
    lbool modular_solve(unsigned lvl);
    void add_clause_expr(expr *fml);
    void addShared(expr_ref_vector const &vars) {
        unsigned v;
        for (expr *e : vars) {
            v = boolVar(e);
            m_shared[v] = true;
        }
    }
    void addPreferred(expr_ref_vector const &vars) {
        unsigned v;
        for (expr *e : vars) {
            v = boolVar(e);
            m_preferred.push_back(v);
        }
        m_picked.resize(m_preferred.size());
    }
        void set_itp(sms_proof_itp* itp) { m_itp = itp; }
        void set_validator(sms_validator* v) { m_validator = v; }
        bool has_var(expr* e, bool_var& v) { return m_expr2var.find(e, v); }
        bool has_expr(bool_var v, expr* &e) {
            if (m_var2expr.size() <= v) return false;
            e = m_var2expr[v].get();
            return true;
        }
        bool is_shared(bool_var v) {
            return m_shared.size() > v && m_shared[v];
        }
    bool_var get_var(expr *e) {
        bool_var v;
        bool found = m_expr2var.find(e, v);
        (void) found;
        SASSERT(found);
        return v;
    }
    expr *get_expr(bool_var v) {
        SASSERT(m_var2expr.size() > v);
        return m_var2expr[v].get();
    }
    void print_var_map() {
        TRACE(
            "satmodsat", for (unsigned i = 0; i < m_var2expr.size(); i++) {
                tout << "expr " << expr_ref(m_var2expr[i].get(), m) << " var "
                     << i << "\n";
            };);
    }
};

class satmodsatcontext {
    ast_manager &m;
    extension *m_solverA;
    extension *m_solverB;
    solver *m_satA;
    solver *m_satB;
    sms_proof_itp* m_itp;
    sms_validator* m_validator;
    void add_cnf_expr_to_solver(extension *s, expr_ref fml);
    std::ostream* m_stream;
  public:
    void addA(expr_ref fml);
    void addB(expr_ref fml);
    void addShared(expr_ref_vector const &vars) {
        sms_solver *a = static_cast<sms_solver *>(m_solverA);
        sms_solver *b = static_cast<sms_solver *>(m_solverB);
        a->addShared(vars);
        b->addShared(vars);
        DEBUG_CODE(for (expr *e : vars) { SASSERT(a->get_var(e) == b->get_var(e)); };);
        a->print_var_map();
        b->print_var_map();
    }
    void addPreferred(expr_ref_vector const &prefA, expr_ref_vector const &prefB) {
        sms_solver *a = static_cast<sms_solver *>(m_solverA);
        a->addPreferred(prefA);
        sms_solver *b = static_cast<sms_solver *>(m_solverB);
        b->addPreferred(prefB);
    }
    satmodsatcontext(ast_manager &am, params_ref const& p) : m(am), m_itp(nullptr), m_validator(nullptr) {
        symbol dratFile = symbol("smsdrat.txt");
        symbol dratFilea = symbol("smsdrata.txt");
        symbol dratFileb = symbol("smsdratb.txt");
        //TODO: Lemma minimization attempts to get_antecedents for
        //each literal in the lemma. However, it sets the probing flag
        //to false, triggering clause learning in sms_solver.
        SASSERT(!p.get_bool("minimize_lemmas", false));
        m_solverA = alloc(sms_solver, m, symbol("A"), PSOLVER_EXT_IDX, p);
        m_solverB = alloc(sms_solver, m, symbol("B"), NSOLVER_EXT_IDX, p);
        sms_solver *a = static_cast<sms_solver *>(m_solverA);
        sms_solver *b = static_cast<sms_solver *>(m_solverB);
        m_stream = alloc(std::ofstream, dratFile.str(), std::ios_base::out);
        a->init_drat(m_stream);
        b->init_drat(m_stream);
        params_ref pa(p), pb(p);
        pa.set_sym("drat.file", dratFilea);
        m_satA = alloc(solver, pa, m.limit());
        m_satA->set_extension(m_solverA);
        pb.set_sym("drat.file", dratFileb);
        m_satB = alloc(solver, pb, m.limit());
        m_satB->set_extension(m_solverB);
        a->set_nSolver(b);
        b->set_pSolver(a);
        b->construct_itp();
        b->set_search_mode(0);
        a->set_prop_mode();
        m_validator = alloc(sms_validator, m);
        a->set_validator(m_validator);
        b->set_validator(m_validator);
    }
    ~satmodsatcontext() {
        dealloc(m_satA);
        dealloc(m_satB);
        dealloc(m_stream);
        dealloc(m_validator);
    }

        void set_itp(sms_proof_itp* itp) {
            m_itp = itp;
            sms_solver *a = static_cast<sms_solver *>(m_solverA);
            sms_solver *b = static_cast<sms_solver *>(m_solverB);
            a->set_itp(m_itp);
            b->set_itp(m_itp);
        }

        bool solve() {
            sms_solver *b = static_cast<sms_solver *>(m_solverB);
            lbool res = b->modular_solve(0);
            if (res == l_false) {
                return false;
            }
            SASSERT(res == l_true);
            return true;
        }

        unsigned get_var(expr* e) {
            sms_solver *b = static_cast<sms_solver *>(m_solverB);
            sms_solver *a = static_cast<sms_solver *>(m_solverA);
            bool_var v;
            VERIFY(b->has_var(e, v) || a->has_var(e, v));
            return v;
        }

        expr* get_expr(bool_var v) {
            sms_solver *b = static_cast<sms_solver *>(m_solverB);
            sms_solver *a = static_cast<sms_solver *>(m_solverA);
            expr* e;
            VERIFY(b->has_expr(v, e) || a->has_expr(v, e));
            return e;
        }

        bool is_shared(bool_var v) {
            sms_solver *b = static_cast<sms_solver *>(m_solverB);
            return b->is_shared(v);
        }
};

    class sat_mod_sat {
        ast_manager &m;
        expr_ref_vector m_shared;
        expr_ref m_a;
        expr_ref m_b;
        satmodsatcontext m_solver;
        void init(expr_ref A, expr_ref B, expr_ref_vector const &shared, expr_ref_vector const &prefA, expr_ref_vector const &prefB);
        public:
            sat_mod_sat(ast_manager &am, const params_ref & p)
                : m(am), m_shared(m), m_a(m), m_b(m), m_solver(m, p) {}
            bool solve(expr_ref A, expr_ref B, expr_ref_vector &shared, expr_ref_vector &prefA, expr_ref_vector &prefB);
            void set_itp(sms_proof_itp* itp) { m_solver.set_itp(itp); }
            unsigned get_var(expr* e) { return m_solver.get_var(e); }
            expr* get_expr(bool_var v) { return m_solver.get_expr(v); }
            bool is_shared(bool_var v) { return m_solver.is_shared(v); }

    };
} // namespace sat
