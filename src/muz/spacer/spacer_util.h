/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    spacer_util.h

Abstract:

    Utility functions for SPACER.

Author:

    Krystof Hoder (t-khoder) 2011-8-19.
    Arie Gurfinkel
    Anvesh Komuravelli

Revision History:

--*/

#pragma once

#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "util/obj_hashtable.h"
#include "util/ref_vector.h"
#include "util/trace.h"
#include "util/vector.h"
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/ast_util.h"
#include "ast/expr_map.h"
#include "model/model.h"

#include "util/stopwatch.h"
#include "muz/spacer/spacer_antiunify.h"

class model;
class model_core;

namespace spacer {

    inline unsigned infty_level () {
        return UINT_MAX;
    }

    inline bool is_infty_level(unsigned lvl) {
        // XXX: level is 16 bits in class pob
        return lvl >= 65535;
    }

    inline unsigned next_level(unsigned lvl) {
        return is_infty_level(lvl)?lvl:(lvl+1);
    }

    inline unsigned prev_level (unsigned lvl) {
        if (is_infty_level(lvl)) return infty_level();
        if (lvl == 0) return 0;
        return lvl - 1;
    }

    struct pp_level {
        unsigned m_level;
        pp_level(unsigned l): m_level(l) {}
    };

    inline std::ostream& operator<<(std::ostream& out, pp_level const& p) {
        if (is_infty_level(p.m_level)) {
            return out << "oo";
        } else {
            return out << p.m_level;
        }
    }

    typedef ptr_vector<app> app_vector;
    typedef ptr_vector<func_decl> decl_vector;
    typedef obj_hashtable<func_decl> func_decl_set;

    /**
       \brief hoist non-boolean if expressions.
    */

    void to_mbp_benchmark(std::ostream &out, const expr* fml, const app_ref_vector &vars);


    // TBD: deprecate by qe::mbp
    /**
     * do the following in sequence
     * 1. use qe_lite to cheaply eliminate vars
     * 2. for remaining boolean vars, substitute using M
     * 3. use MBP for remaining array and arith variables
     * 4. for any remaining arith variables, substitute using M
     */
    void qe_project (ast_manager& m, app_ref_vector& vars,
                     expr_ref& fml, model &mdl,
                     bool reduce_all_selects=false,
                     bool native_mbp=false,
                     bool dont_sub=false);

    // deprecate
    void qe_project (ast_manager& m, app_ref_vector& vars, expr_ref& fml,
                     model_ref& M, expr_map& map);

    // TBD: sort out
    void expand_literals(ast_manager &m, expr_ref_vector& conjs);
    expr_ref_vector compute_implicant_literals(model &mdl,
                                    expr_ref_vector &formula);
    void simplify_bounds (expr_ref_vector &lemmas);
    void normalize(expr *e, expr_ref &out, bool use_simplify_bounds = true, bool factor_eqs = false);

    void normalize_order(expr *e, expr_ref &out);
    /**
     * Ground expression by replacing all free variables by skolem
     * constants. On return, out is the resulting expression, and vars is
     * a map from variable ids to corresponding skolem constants.
     */
    void ground_expr (expr *e, expr_ref &out, app_ref_vector &vars);

    void mbqi_project(model &mdl, app_ref_vector &vars, expr_ref &fml);

    bool contains_selects (expr* fml, ast_manager& m);
    void get_select_indices (expr* fml, app_ref_vector& indices);

    void find_decls (expr* fml, app_ref_vector& decls, std::string& prefix);

    /**
     * extended pretty-printer
     * used for debugging
     * disables aliasing of common sub-expressions
     */
    struct mk_epp : public mk_pp {
        params_ref m_epp_params;
        expr_ref m_epp_expr;
    mk_epp(ast *t, ast_manager &m, unsigned indent = 0, unsigned num_vars = 0, char const * var_prefix = nullptr);
        void rw(expr *e, expr_ref &out);
    };

    bool is_clause(ast_manager &m, expr *n); 
    bool is_literal(ast_manager &m, expr *n);
    bool is_atom(ast_manager &m, expr *n);

    // set f to true in model
    void set_true_in_mdl(model &model, func_decl *f);
    /// Returns number of free variables in a given expression
    unsigned get_num_vars(expr *e);
    void get_uninterp_consts(expr *a, expr_ref_vector &out);
    bool has_nonlinear_mul(expr *e, ast_manager &m);

    /// Checks whether there is a var*u_c term
    bool has_nonlinear_var_mul(expr *e, ast_manager &m);

    // check whether lit is an instance of mono_var_pattern
    bool is_mono_var(expr *lit, ast_manager &m, arith_util &a_util);

    // a mono_var_pattern has only one variable in the whole expression and is
    // linear. lit is the literal with the variable
    bool should_conjecture(const expr_ref &p, expr_ref &lit);

    /// Drop all literals that numerically match \p lit, from \p fml_vec.
    ///
    /// \p abs_fml holds the result. Returns true if any literal has been dropped
    bool drop_lit(expr_ref_vector &in, expr_ref &lit, expr_ref_vector &out);

    /// Returns true if range of s is numeric
    bool is_numeric_sub(substitution &s);

    bool contains_mod(expr_ref e);

    //checks whether any sub expression of \p e is of sort Real
    bool contains_real(expr_ref e);

    /// try to compute \p t and \p c such that (t <= c) ==> lit and c is a
    /// numeral
    bool under_approx_using_le(expr *lit, expr_ref &t, expr_ref &c);

    // multiply fml with num and simplify rationals to ints
    // fml should be in LIA/LRA/Arrays
    // assumes that fml is a sum of products
    void mul_by_rat(expr_ref &fml, rational num);

    // get all numeral values in the formula
    void extract_nums(expr_ref fml, vector<rational> &res);

    //returns whether predicate \p pred represents a recursive function
    bool is_rf_pred(func_decl* pred);

    // remove all applications of rf in res;
    void drop_rf_app(expr_ref_vector& res);

    // get the recfun definition corresponding to rf pred pred
    func_decl* get_rf_pred(func_decl* pred, ast_manager &m);

    // check whether mdl satisfies get_rf(pred)(arg1) == arg2
    bool check_mdl_rf(func_decl* pred, expr* arg1, expr* arg2, model &mdl);

    //contains a recfun term
    bool contains_rf_app(expr *e, ast_manager& m);

    bool contains_rf_app(expr_ref_vector& cube);
}

