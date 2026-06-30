/**
 * CryptoMiniSat C Wrapper for Python ctypes
 * 
 * 桥接 Python (Class.py) 和 CryptoMiniSat5 C++ 库。
 * 编译: g++ -shared -fPIC -o libcmsat_wrapper.so cmsat_wrapper.cpp \
 *        -I cryptominisat/build/include/cryptominisat5 \
 *        -L cryptominisat/build/lib -lcryptominisat5 \
 *        -Wl,-rpath,./cryptominisat/build/lib
 */

#include "cryptominisat.h"
#include <vector>
#include <cstdint>
#include <cstdlib>

using namespace CMSat;

#define SAT 10
#define UNSAT 20

typedef SATSolver* CMSSolver;

// ===================== 生命周期 =====================

extern "C" CMSSolver cmsat_create() {
    return new SATSolver();
}

extern "C" void cmsat_destroy(CMSSolver solver) {
    delete solver;
}

// ===================== 子句管理 =====================

extern "C" bool cmsat_add_clause(CMSSolver solver, const int* lits, int len) {
    std::vector<Lit> clause;
    for (int i = 0; i < len; i++) {
        if (lits[i] == 0) break;
        int var_idx = abs(lits[i]) - 1;
        bool sign = (lits[i] < 0);
        // 确保变量存在
        while (var_idx >= (int)solver->nVars()) {
            solver->new_var();
        }
        clause.push_back(Lit(var_idx, sign));
    }
    return solver->add_clause(clause);
}

// ===================== 求解 =====================

extern "C" int cmsat_solve(CMSSolver solver) {
    lbool result = solver->solve();
    if (result == l_True)  return SAT;
    if (result == l_False) return UNSAT;
    return 0;  // UNKNOWN
}

extern "C" int cmsat_solve_with_assumptions(CMSSolver solver, const int* assumptions, int len) {
    std::vector<Lit> assumps;
    for (int i = 0; i < len; i++) {
        int var_idx = abs(assumptions[i]) - 1;
        bool sign = (assumptions[i] < 0);
        while (var_idx >= (int)solver->nVars()) {
            solver->new_var();
        }
        assumps.push_back(Lit(var_idx, sign));
    }
    lbool result = solver->solve(&assumps);
    if (result == l_True)  return SAT;
    if (result == l_False) return UNSAT;
    return 0;
}

// ===================== 模型查询 =====================

extern "C" int cmsat_model_value(CMSSolver solver, int var) {
    // var 是 1-based
    if (var < 1 || var > (int)solver->nVars()) return 0;
    const auto& model = solver->get_model();
    lbool val = model[var - 1];
    if (val == l_True)  return 1;
    if (val == l_False) return -1;
    return 0;  // l_Undef
}

extern "C" int cmsat_max_var(CMSSolver solver) {
    return (int)solver->nVars();
}

// ===================== 冲突分析 =====================

extern "C" int* cmsat_get_conflict(CMSSolver solver, int* out_size) {
    const auto& conflict = solver->get_conflict();
    *out_size = (int)conflict.size();
    if (conflict.empty()) return nullptr;
    
    int* arr = (int*)malloc(conflict.size() * sizeof(int));
    for (size_t i = 0; i < conflict.size(); i++) {
        int var = (int)conflict[i].var() + 1;  // 转回 1-based
        bool sign = conflict[i].sign();
        arr[i] = sign ? -var : var;
    }
    return arr;
}

// ===================== 变量管理 =====================

extern "C" void cmsat_var_enlarge_to(CMSSolver solver, int v) {
    while ((int)solver->nVars() < v) {
        solver->new_var();
    }
}

// ===================== 化简 =====================

extern "C" void cmsat_simplify(CMSSolver solver) {
    solver->simplify();
}

// ===================== XOR 支持 =====================

extern "C" bool cmsat_add_xor_gate(CMSSolver solver, unsigned a, unsigned b, unsigned c) {
    // XOR 门: c = a XOR b  等价于  a XOR b XOR c = false
    std::vector<unsigned> vars = {a, b, c};
    return solver->add_xor_clause(vars, false);
}

extern "C" bool cmsat_add_xor_clause_lits(CMSSolver solver, const int* lits, int len, bool rhs) {
    // 将 int 风格文字 (正=变量, 负=否定) 转为 Lit 向量
    std::vector<Lit> xlits;
    for (int i = 0; i < len; i++) {
        int var_idx = abs(lits[i]) - 1;
        bool sign = (lits[i] < 0);
        while (var_idx >= (int)solver->nVars()) {
            solver->new_var();
        }
        xlits.push_back(Lit(var_idx, sign));
    }
    return solver->add_xor_clause(xlits, rhs);
}

// ===================== 随机种子 =====================

extern "C" void cmsat_set_seed(CMSSolver solver, unsigned seed) {
    solver->set_seed(seed);
}
