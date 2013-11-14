/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    qe_arith.cpp

Abstract:

    Simple projection function for real arithmetic based on Loos-W.

Author:

    Nikolaj Bjorner (nbjorner) 2013-09-12

Revision History:


--*/

#include "qe_arith.h"
#include "qe_util.h"
#include "arith_decl_plugin.h"
#include "ast_pp.h"
#include "th_rewriter.h"
#include "expr_functors.h"

namespace qe {
    
    class arith_project_util {
        ast_manager& m;
        arith_util   a;
        th_rewriter  m_rw;
        expr_ref_vector  m_lits;
        expr_ref_vector  m_terms;
        vector<rational> m_coeffs;
        svector<bool>    m_strict;
        svector<bool>    m_eq;
        scoped_ptr<contains_app> m_var;

        struct cant_project {};

        void is_linear(rational const& mul, expr* t, rational& c, expr_ref_vector& ts) {
            expr* t1, *t2;
            rational mul1;
            if (t == m_var->x()) {
                c += mul;
            }
            else if (a.is_mul(t, t1, t2) && a.is_numeral(t1, mul1)) {
                is_linear(mul* mul1, t2, c, ts);
            }
            else if (a.is_mul(t, t1, t2) && a.is_numeral(t2, mul1)) {
                is_linear(mul* mul1, t1, c, ts);
            }
            else if (a.is_add(t)) {
                app* ap = to_app(t);
                for (unsigned i = 0; i < ap->get_num_args(); ++i) {
                    is_linear(mul, ap->get_arg(i), c, ts);
                }
            }
            else if (a.is_sub(t, t1, t2)) {
                is_linear(mul,  t1, c, ts);
                is_linear(-mul, t2, c, ts);
            }
            else if (a.is_uminus(t, t1)) {
                is_linear(-mul, t1, c, ts);
            }
            else if (a.is_numeral(t, mul1)) {
                ts.push_back(a.mk_numeral(mul*mul1, m.get_sort(t)));
            }
            else if ((*m_var)(t)) {
                IF_VERBOSE(1, verbose_stream() << "can't project:" << mk_pp(t, m) << "\n";);
                throw cant_project();
            }
            else if (mul.is_one()) {
                ts.push_back(t);
            }
            else {
                ts.push_back(a.mk_mul(a.mk_numeral(mul, m.get_sort(t)), t));
            }
        }

        bool is_linear(expr* lit, rational& c, expr_ref& t, bool& is_strict, bool& is_eq, bool& is_diseq) {
            if (!(*m_var)(lit)) {
                return false;
            }
            expr* e1, *e2;
            c.reset();
            sort* s;
            expr_ref_vector ts(m);            
            bool is_not = m.is_not(lit, lit);
            rational mul(1);
            if (is_not) {
                mul.neg();
            }
            SASSERT(!m.is_not(lit));
            if (a.is_le(lit, e1, e2) || a.is_ge(lit, e2, e1)) {
                is_linear( mul, e1, c, ts);
                is_linear(-mul, e2, c, ts);
                s = m.get_sort(e1);
                is_strict = is_not;
            }
            else if (a.is_lt(lit, e1, e2) || a.is_gt(lit, e2, e1)) {
                is_linear( mul, e1, c, ts);
                is_linear(-mul, e2, c, ts);
                s = m.get_sort(e1);
                is_strict = !is_not;
            }
            else if (m.is_eq(lit, e1, e2)) {
                is_linear( mul, e1, c, ts);
                is_linear(-mul, e2, c, ts);
                s = m.get_sort(e1);
                if (is_not) is_diseq = true;
                else is_eq = true;
            }            
            else {
                IF_VERBOSE(1, verbose_stream() << "can't project:" << mk_pp(lit, m) << "\n";);
                throw cant_project();
            }
            if (ts.empty()) {
                t = a.mk_numeral(rational(0), s);
            }
            else {
                t = a.mk_add(ts.size(), ts.c_ptr());
            }
            return true;
        }

        void project(model& mdl, expr_ref_vector& lits) {
            unsigned num_pos = 0;
            unsigned num_neg = 0;
            bool use_eq = false;
            expr_ref_vector new_lits(m);
            expr_ref eq_term (m);

            m_lits.reset ();
            m_terms.reset();
            m_coeffs.reset();
            m_strict.reset();
            m_eq.reset ();

            for (unsigned i = 0; i < lits.size(); ++i) {
                rational c(0);
                expr_ref t(m);
                bool is_strict = false;
                bool is_eq = false;
                bool is_diseq = false;
                if (is_linear(lits.get (i), c, t, is_strict, is_eq, is_diseq)) {
                    if (c.is_zero()) {
                        m_rw(lits.get (i), t);
                        new_lits.push_back(t);
                    } else if (is_eq) {
                        if (!use_eq) {
                            // c*x + t = 0  <=>  x = -t/c
                            eq_term = mk_mul (-(rational::one ()/c), t);
                            use_eq = true;
                        }
                        m_lits.push_back (lits.get (i));
                        m_coeffs.push_back(c);
                        m_terms.push_back(t);
                        m_strict.push_back(false);
                        m_eq.push_back (true);
                    } else {
                        if (is_diseq) {
                            // c*x + t != 0
                            // find out whether c*x + t < 0, or c*x + t > 0
                            expr_ref cx (m), cxt (m), val (m);
                            rational r;
                            cx = mk_mul (c, m_var->x());
                            cxt = mk_add (cx, t);
                            VERIFY(mdl.eval(cxt, val));
                            VERIFY(a.is_numeral(val, r));
                            SASSERT (r > rational::zero () || r < rational::zero ());
                            if (r > rational::zero ()) {
                                c = -c;
                                t = mk_mul (-(rational::one()), t);
                            }
                            is_strict = true;
                        }
                        m_lits.push_back (lits.get (i));
                        m_coeffs.push_back(c);
                        m_terms.push_back(t);
                        m_strict.push_back(is_strict);
                        m_eq.push_back (false);
                        if (c.is_pos()) {
                            ++num_pos;
                        }
                        else {
                            ++num_neg;
                        }                    
                    }
                }
                else {
                    new_lits.push_back(lits.get (i));
                }
            }
            if (use_eq) {
                TRACE ("qe",
                        tout << "Using equality term: " << mk_pp (eq_term, m) << "\n";
                      );
                // substitute eq_term for x everywhere
                for (unsigned i = 0; i < m_lits.size(); ++i) {
                    expr_ref cx (m), cxt (m), z (m), result (m);
                    cx = mk_mul (m_coeffs[i], eq_term);
                    cxt = mk_add (cx, m_terms.get(i));
                    z = a.mk_numeral(rational(0), m.get_sort(eq_term));
                    if (m_eq[i]) {
                        // c*x + t = 0
                        result = a.mk_eq (cxt, z);
                    } else if (m_strict[i]) {
                        // c*x + t < 0
                        result = a.mk_lt (cxt, z);
                    } else {
                        // c*x + t <= 0
                        result = a.mk_le (cxt, z);
                    }
                    m_rw (result);
                    new_lits.push_back (result);
                }
            }
            lits.reset();
            lits.append(new_lits);
            if (use_eq || num_pos == 0 || num_neg == 0) {
                return;
            }
            bool use_pos = num_pos < num_neg;
            unsigned max_t = find_max(mdl, use_pos);

            expr_ref new_lit (m);
            for (unsigned i = 0; i < m_lits.size(); ++i) {
                if (i != max_t) {
                    if (m_coeffs[i].is_pos() == use_pos) {
                        new_lit = mk_le(i, max_t);
                    }
                    else {
                        new_lit = mk_lt(i, max_t);
                    }
                    lits.push_back(new_lit);
                    TRACE ("qe",
                            tout << "Old literal: " << mk_pp (m_lits.get (i), m) << "\n";
                            tout << "New literal: " << mk_pp (new_lit, m) << "\n";
                          );
                }
            }
        }

        unsigned find_max(model& mdl, bool do_pos) {
            unsigned result;
            bool found = false;
            bool found_strict = false;
            rational found_val(0), r, found_c;
            expr_ref val(m);
            for (unsigned i = 0; i < m_terms.size(); ++i) {
                rational const& ac = m_coeffs[i];
                if (!m_eq[i] && ac.is_pos() == do_pos) {
                    VERIFY(mdl.eval(m_terms.get (i), val));
                    VERIFY(a.is_numeral(val, r));
                    r /= abs(ac);
                    IF_VERBOSE(1, verbose_stream() << "max: " << mk_pp(m_terms.get (i), m) << " " << r << " " <<
                                (!found || r > found_val || (r == found_val && !found_strict && m_strict[i])) << "\n";);
                    if (!found || r > found_val || (r == found_val && !found_strict && m_strict[i])) {
                        result = i;
                        found_val = r;
                        found_c = ac;
                        found = true;
                        found_strict = m_strict[i];
                    }
                }
            }
            SASSERT(found);
            if (a.is_int(m_var->x()) && !found_c.is_one()) {
                throw cant_project();
            }
            return result;
        }

        // ax + t <= 0
        // bx + s <= 0
        // a and b have different signs.
        // Infer: a|b|x + |b|t + |a|bx + |a|s <= 0
        // e.g.   |b|t + |a|s <= 0
        expr_ref mk_lt(unsigned i, unsigned j) {
            rational const& ac = m_coeffs[i];
            rational const& bc = m_coeffs[j];
            SASSERT(ac.is_pos() != bc.is_pos());
            SASSERT(ac.is_neg() != bc.is_neg());
            expr_ref bt (m), as (m), ts (m), z (m);
            expr* t = m_terms.get (i);
            expr* s = m_terms.get (j);
            bt = mk_mul(abs(bc), t);
            as = mk_mul(abs(ac), s);
            ts = mk_add(bt, as);
            z  = a.mk_numeral(rational(0), m.get_sort(t));
            expr_ref result1(m), result2(m);
            if (m_strict[i] || m_strict[j]) {
                result1 = a.mk_lt(ts, z);
            }
            else {
                result1 = a.mk_le(ts, z);
            }
            m_rw(result1, result2);
            return result2;
        }

        // ax + t <= 0
        // bx + s <= 0
        // a and b have same signs.
        // encode:// t/|a| <= s/|b|
        // e.g.   |b|t <= |a|s
        expr_ref mk_le(unsigned i, unsigned j) {
            rational const& ac = m_coeffs[i];
            rational const& bc = m_coeffs[j];
            SASSERT(ac.is_pos() == bc.is_pos());
            SASSERT(ac.is_neg() == bc.is_neg());
            expr_ref bt (m), as (m);
            expr* t = m_terms.get (i);
            expr* s = m_terms.get (j);
            bt = mk_mul(abs(bc), t);
            as = mk_mul(abs(ac), s);
            expr_ref result1(m), result2(m);
            if (!m_strict[j] && m_strict[i]) {
                result1 = a.mk_lt(bt, as);
            }
            else {
                result1 = a.mk_le(bt, as);
            }
            m_rw(result1, result2);
            return result2;
        }


        expr* mk_add(expr* t1, expr* t2) {
            return a.mk_add(t1, t2);
        }
        expr* mk_mul(rational const& r, expr* t2) {
            expr* t1 = a.mk_numeral(r, m.get_sort(t2));
            return a.mk_mul(t1, t2);
        }

    public:
        arith_project_util(ast_manager& m): 
            m(m), a(m), m_rw(m), m_lits (m), m_terms (m) {}

        expr_ref operator()(model& mdl, app_ref_vector& vars, expr_ref_vector const& lits) {
            app_ref_vector new_vars(m);
            expr_ref_vector result(lits);
            for (unsigned i = 0; i < vars.size(); ++i) {
                app* v = vars.get (i);
                m_var = alloc(contains_app, m, v);
                try {
                    project(mdl, result);
                    TRACE("qe", tout << "projected: " << mk_pp(v, m) << " ";
                          for (unsigned i = 0; i < result.size(); ++i) {
                              tout << mk_pp(result.get (i), m) << "\n";
                          });
                }
                catch (cant_project) {
                    IF_VERBOSE(1, verbose_stream() << "can't project:" << mk_pp(v, m) << "\n";);
                    new_vars.push_back(v);
                }
            }
            vars.reset();
            vars.append(new_vars);
            return qe::mk_and(result);
        }  
    };

    expr_ref arith_project(model& mdl, app_ref_vector& vars, expr_ref_vector const& lits) {
        ast_manager& m = vars.get_manager();
        arith_project_util ap(m);
        return ap(mdl, vars, lits);
    }

    expr_ref arith_project(model& model, app_ref_vector& vars, expr* fml) {
        ast_manager& m = vars.get_manager();
        arith_project_util ap(m);
        expr_ref_vector lits(m);
        qe::flatten_and(fml, lits);
        return ap(model, vars, lits);
    }

}
