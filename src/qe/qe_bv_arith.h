/***
 */
#pragma once
#include "ast/arith_decl_plugin.h"
#include "model/model.h"
#include "qe/qe_mbp.h"

namespace qe {

/**
   MBP for BV
 */

class bv_project_plugin : public project_plugin {
    struct imp;
    imp *m_imp;

  public:
    bv_project_plugin(ast_manager &m);
    ~bv_project_plugin() override;
    bool operator()(model &model, app *var, app_ref_vector &vars,
                    expr_ref_vector &lits) override;
    bool solve(model &model, app_ref_vector &vars,
               expr_ref_vector &lits) override;
    family_id get_family_id() override;
    void operator()(model &model, app_ref_vector &vars,
                    expr_ref_vector &lits) override;
    vector<def> project(model &model, app_ref_vector &vars,
                        expr_ref_vector &lits) override;

    opt::inf_eps maximize(expr_ref_vector const &fmls, model &mdl, app *t,
                          expr_ref &ge, expr_ref &gt);

    void saturate(model &model, func_decl_ref_vector const &shared,
                  expr_ref_vector &lits) override;
    /**
     * \brief check if formulas are purified, or leave it to caller to ensure
     * that arithmetic variables nested under foreign functions are handled
     * properly.
     */
    void set_check_purified(bool check_purified);
};
}; // namespace qe
