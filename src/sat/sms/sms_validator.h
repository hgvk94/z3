#pragma once
#include "ast/ast.h"
#include "ast/ast_util.h"
#include "sat/sat_justification.h"
#include "sat/sat_types.h"
#include "sat/sms/sms_solver.h"
#include "util/debug.h"
#include "util/memory_manager.h"
#include "util/params.h"
#include "util/sat_literal.h"
#include "util/vector.h"
namespace sat {
    //hack. copy past definitions. change!!!
#define NSOLVER_EXT_IDX 2
#define PSOLVER_EXT_IDX 1

    class validator {
        ast_manager& m;
        solver* s;

    public:

    validator(ast_manager& man): m(man) {
            params_ref p;
            s = alloc(solver, p, m.limit());
        }

        ~validator() {
            dealloc(s);
        }

        void add_var() { s->add_var(true); }
        void rup(unsigned sz, literal const* lc) {
            if (sz == 0) {
                SASSERT(s->inconsistent());
                return;
            }
            if (s->inconsistent()) {
                TRACE("satmodsat_validate", tout << "already unsat\n";);
                return;
            }
            SASSERT(s->at_base_lvl());
            s->push();
            justification js = justification(1);
            for(unsigned i = 0; i < sz; i++) {
                s->assign(~lc[i], js);
            }
            bool sat = s->propagate(false);
            CTRACE("satmodsat_validate", sat, s->display_assignment(tout));
            SASSERT(!sat);
            s->pop(1);
            literal_vector tmp(sz, lc);
            s->add_clause(sz, tmp.data(), sat::status::asserted());
            s->propagate(false);
        }

        void add(unsigned sz, literal const* lc) {
            literal_vector tmp(sz, lc);
            s->add_clause(sz, tmp.data(), sat::status::asserted());
            s->propagate(false);
        }
    };

    class sms_validator {
        validator* s1;
        validator* s2;
        vector<status> m_trail;

    public:
        sms_validator(ast_manager& man) {
            s1 = alloc(validator, man);
            s2 = alloc(validator, man);
        }
        ~sms_validator() {
            dealloc(s1);
            dealloc(s2);
        }

        void add_var(unsigned id) {
            validator* s = id == NSOLVER_EXT_IDX ? s2 : s1;
            s->add_var();
        }

        void validate(status st, unsigned sz, literal const* lc, unsigned id) {
            validator* s = id == NSOLVER_EXT_IDX ? s2 : s1;
            validator* o = id == NSOLVER_EXT_IDX ? s1 : s2;
            TRACE("satmodsat_validate", tout << "adding clause to " << id << "\n";);
            switch (st.m_st) {
                case status::st::input:
                    s->add(sz, lc);
                    break;
                case status::st::asserted:
                    if (m_trail[m_trail.size() - 1].is_copied())
                        s->add(sz, lc);
                    else
                        s->rup(sz, lc);
                    break;
                case status::st::redundant:
                    if (m_trail[m_trail.size() - 1].is_copied())
                        s->add(sz, lc);
                    else
                        s->rup(sz, lc);
                    break;
                case status::st::copied:
                    o->rup(sz, lc);
                    s->add(sz, lc);
                    break;
                case status::st::deleted:
                    break;
            }
            m_trail.push_back(st);
        }
    };
}
