#pragma once
#include "ast/ast.h"
#include "sat/sat_clause.h"
#include "sat/sat_justification.h"
#include "util/sat_literal.h"
#include "util/hashtable.h"

typedef std::tuple<sat::literal_vector, sat::status, sat::clause*, unsigned> lv_st;
    //hack. copy past definitions. change!!!
#define NSOLVER_EXT_IDX_TMP 1
#define PSOLVER_EXT_IDX_TMP 0
namespace sat {
    class sms_proof_trim {
        ast_manager&    m;
        solver*         m_solvers[2];
        vector<lv_st> m_ctrail;
        //copy pasted from sat_proof_trim
        struct hash {
            unsigned operator()(literal_vector const& v) const {
                return string_hash((char const*)v.begin(), v.size()*sizeof(literal), 3);
            }
        };
        struct eq {
            bool operator()(literal_vector const& a, literal_vector const& b) const {
                return a == b;
            }
        };
        //maps a clause in the sat solver to its index in m_trail
        map<literal_vector, unsigned, hash, eq> m_clauses[2];
        u_map<unsigned> m_units[2];
        u_map<unsigned> m_binary[2];

        //defined in paper
        map<literal_vector, vector<unsigned>, hash, eq> m_deps;
        hashtable<literal_vector, hash, eq> m_mark;
        bool is_marked(literal_vector& lc) { return m_mark.contains(lc); }
        void mark(literal_vector& lc) { m_mark.insert(lc); }
        void mark(lv_st c) { mark(std::get<0>(c)); }
        bool is_fwd_cp(status st) { return st.is_copied() && st.get_src() == PSOLVER_EXT_IDX_TMP; }
        bool is_bwd_cp(status st) { return st.is_copied() && st.get_src() == NSOLVER_EXT_IDX_TMP; }
        bool is_marked(lv_st c) { return is_marked(std::get<0>(c)); }
        bool is_null(lv_st c) { return std::get<0>(c).size() == 1 && std::get<0>(c)[0] == null_literal; }

        unsigned get_clause_index(literal l, justification js, unsigned idx);
        void get_dep_cp(literal_vector const& cl, vector<literal_vector>& op);
        void mark_clause(unsigned i, literal_vector const& cl);
        void mark_dep_clauses(literal_vector const& cl, unsigned idx);
        void rup(unsigned i);
        void remove_from_sol(unsigned i);
        void mk_horn(literal_vector& v, vector<literal_vector>& op);
    public:
        void add_var(unsigned i);
        void log_clause(status s, unsigned sz, literal const *c, unsigned idx);
        void trim();
        sms_proof_trim(params_ref const& p, ast_manager& m);
        ~sms_proof_trim();
    };
}
