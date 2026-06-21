import subprocess
import os
import tempfile
from typing import List, Dict, Set, Optional, Tuple
import ctypes


state_count = 0


class Variable:
    def __init__(self, dimacs_index, name = "", type = "", type_index = 0, prime = 0):
        self.dimacs_var = dimacs_index
        self.name = name
        if type in ['i', 'o', 'l', 'a']:
            # 更新type属性为合法类型
            self.name = type 
            s = f"{type}{str(type_index)}"  
            if prime == 1:
                s += "'"  
            self.name = s 


class SATSolver:
    
    def __init__(self, backend=None):
        if backend is None:
            # 从环境变量读取后端选择 (方便外部切换而不改代码)
            backend = os.environ.get("BLIF_SOLVER_BACKEND", "auto")
        self.clauses = []
        self.current_clause = []
        self.assumptions = []
        self.pre_assumptions = []
        self.max_variable = 0
        self.simplified_cnf = []
        self.solver = None
        
        # 通用常量
        self.SAT = 1
        self.UNSAT = 0
        self.UNKNOWN = -1
        
        # 状态变量
        self.solve_result = self.UNKNOWN
        self.var_values = {}
        self.failed_assumptions = []
        self.clear_flag = False
        
        # 求解器初始化
        if backend == "minisat":
            self._init_minisat()
        elif backend == "cmsat" or backend == "auto":
            try:
                self._init_cryptominisat()
            except Exception as e:
                if backend == "cmsat":
                    print(f"CryptoMiniSat初始化失败：{str(e)}")
                    raise
                else:
                    # auto模式下CMS失败则回退到MiniSat
                    print(f"CryptoMiniSat不可用({str(e)}), 回退到MiniSat")
                    self._init_minisat()
        else:
            raise ValueError(f"未知后端: {backend}, 可选: cmsat, minisat, auto")

    def _init_cryptominisat(self):
        """初始化 CryptoMiniSat 后端"""
        cms_lib_path = os.path.abspath(
            "/home/lyj238/wdl/blif/cryptominisat/build/lib/libcryptominisat5.so"
        )
        ctypes.CDLL(cms_lib_path, mode=ctypes.RTLD_GLOBAL)
        
        lib_path = os.path.abspath("/home/lyj238/wdl/blif/libcmsat_wrapper.so")
        self.lib = ctypes.CDLL(lib_path)
        self._setup_cmsat_functions()
        self.solver = self.lib.cmsat_create()
        seed_str = os.environ.get("CMSAT_SEED", "")
        if seed_str:
            self.lib.cmsat_set_seed(self.solver, int(seed_str))
        self.backend = "cmsat"
    
    def _init_minisat(self):
        """初始化 MiniSat 后端"""
        lib_path = os.path.abspath("/home/lyj238/wdl/IC3/libminisat_wrapper.so")
        self.lib = ctypes.CDLL(lib_path)
        self._setup_minisat_functions()
        self.solver = self.lib.minisat_create()
        self.backend = "minisat"
    
    def _setup_cmsat_functions(self):
        """设置 CryptoMiniSat C++ 库函数原型"""
        self.lib.cmsat_create.restype = ctypes.c_void_p
        self.lib.cmsat_destroy.argtypes = [ctypes.c_void_p]
        self.lib.cmsat_add_clause.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_int), ctypes.c_int]
        self.lib.cmsat_add_clause.restype = ctypes.c_bool
        self.lib.cmsat_solve.argtypes = [ctypes.c_void_p]
        self.lib.cmsat_solve.restype = ctypes.c_int
        self.lib.cmsat_solve_with_assumptions.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_int), ctypes.c_int]
        self.lib.cmsat_solve_with_assumptions.restype = ctypes.c_int
        self.lib.cmsat_model_value.argtypes = [ctypes.c_void_p, ctypes.c_int]
        self.lib.cmsat_model_value.restype = ctypes.c_int
        self.lib.cmsat_max_var.argtypes = [ctypes.c_void_p]
        self.lib.cmsat_max_var.restype = ctypes.c_int
        self.lib.cmsat_get_conflict.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_int)]
        self.lib.cmsat_get_conflict.restype = ctypes.POINTER(ctypes.c_int)
        self.lib.cmsat_var_enlarge_to.argtypes = [ctypes.c_void_p, ctypes.c_int]
        self.lib.cmsat_var_enlarge_to.restype = None
        self.lib.cmsat_simplify.argtypes = [ctypes.c_void_p]
        self.lib.cmsat_simplify.restype = None
        self.lib.cmsat_add_xor_gate.argtypes = [ctypes.c_void_p, ctypes.c_uint, ctypes.c_uint, ctypes.c_uint]
        self.lib.cmsat_add_xor_gate.restype = ctypes.c_bool
        self.lib.cmsat_add_xor_clause_lits.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_int), ctypes.c_int, ctypes.c_bool]
        self.lib.cmsat_add_xor_clause_lits.restype = ctypes.c_bool
        self.lib.cmsat_set_seed.argtypes = [ctypes.c_void_p, ctypes.c_uint]
        self.lib.cmsat_set_seed.restype = None

    def _setup_minisat_functions(self):
        """设置 MiniSat C++ 库函数原型"""
        self.lib.minisat_create.restype = ctypes.c_void_p
        self.lib.minisat_destroy.argtypes = [ctypes.c_void_p]
        self.lib.minisat_add_clause.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_int), ctypes.c_int]
        self.lib.minisat_add_clause.restype = ctypes.c_bool
        self.lib.minisat_solve.argtypes = [ctypes.c_void_p, ctypes.c_bool]
        self.lib.minisat_solve.restype = ctypes.c_int
        self.lib.minisat_set_assumptions.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_int), ctypes.c_int]
        self.lib.minisat_model_value.argtypes = [ctypes.c_void_p, ctypes.c_int]
        self.lib.minisat_model_value.restype = ctypes.c_int
        self.lib.minisat_max_var.argtypes = [ctypes.c_void_p]
        self.lib.minisat_max_var.restype = ctypes.c_int
        self.lib.minisat_clear_assumptions.argtypes = [ctypes.c_void_p]
        self.lib.minisat_get_failed_assumptions.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_int)]
        self.lib.minisat_get_failed_assumptions.restype = ctypes.POINTER(ctypes.c_int)
        self.lib.minisat_var_enlarge_to.argtypes = [ctypes.c_void_p, ctypes.c_int]
        self.lib.minisat_var_enlarge_to.restype = None
        self.lib.minisat_simplify.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_int)]
        self.lib.minisat_simplify.restype = ctypes.POINTER(ctypes.c_int)
        self.lib.minisat_free_simplified_cnf.argtypes = [ctypes.POINTER(ctypes.c_int)]
        self.lib.minisat_free_simplified_cnf.restype = None
        self.lib.minisat_perform_simplify.argtypes = [ctypes.c_void_p]
        self.lib.minisat_perform_simplify.restype = None
        self.lib.minisat_get_raw_cnf.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_int)]
        self.lib.minisat_get_raw_cnf.restype = ctypes.POINTER(ctypes.c_int)
        self.lib.minisat_freeze_var.argtypes = [ctypes.c_void_p, ctypes.c_int]
        self.lib.minisat_freeze_var.restype = None
        self.lib.minisat_unfreeze_var.argtypes = [ctypes.c_void_p, ctypes.c_int]
        self.lib.minisat_unfreeze_var.restype = None

    def __del__(self):
        """析构函数"""
        if hasattr(self, 'solver') and self.solver:
            if self.backend == "cmsat":
                self.lib.cmsat_destroy(self.solver)
            elif self.backend == "minisat":
                self.lib.minisat_destroy(self.solver)
    
    def simplify(self) -> List[int]:
        if self.backend == "cmsat":
            self.lib.cmsat_simplify(self.solver)
            self.simplified_cnf = []
            for clause in self.clauses:
                for lit in clause:
                    self.simplified_cnf.append(lit)
                self.simplified_cnf.append(0)
            return self.simplified_cnf
        else:
            # MiniSat
            out_size = ctypes.c_int()
            simplified_ptr = self.lib.minisat_simplify(self.solver, ctypes.byref(out_size))
            self.simplified_cnf = []
            if out_size.value > 0:
                self.simplified_cnf = [simplified_ptr[i] for i in range(out_size.value)]
                self.lib.minisat_free_simplified_cnf(simplified_ptr)
            return self.simplified_cnf
    
    def perform_simplify(self) -> None:
        """仅执行简化，不获取简化后的 CNF（性能更好）"""
        if self.backend == "cmsat":
            self.lib.cmsat_simplify(self.solver)
        else:
            self.lib.minisat_perform_simplify(self.solver)
    
    def get_simplified_cnf(self) -> List[int]:
        """获取上次简化后的 CNF"""
        return self.simplified_cnf.copy()
    
    def show_simplified_cnf(self) -> None:
        """显示简化后的 CNF"""
        if not self.simplified_cnf:
            print("No simplified CNF available. Call simplify() first.")
            return
        
        print("Simplified CNF:")
        clause = []
        for lit in self.simplified_cnf:
            if lit == 0:
                if clause:
                    print("  " + " ".join(str(l) for l in clause))
                    clause = []
            else:
                clause.append(lit)
        
        # 打印最后一个子句（如果有）
        if clause:
            print("  " + " ".join(str(l) for l in clause))
    
    
    def var_enlarge_to(self, v: int) -> None:
        """
        扩展变量到至少 v 个（确保变量索引 1 到 v 都存在）
        参数 v: 目标变量数量（DIMACS 格式，从 1 开始）
        """
        if self.backend == "cmsat":
            self.lib.cmsat_var_enlarge_to(self.solver, v)
        else:
            self.lib.minisat_var_enlarge_to(self.solver, v)
        if v > self.max_variable:
            self.max_variable = v
            
    def add(self, dimacs_lit: int) -> bool:
        """
        添加文字到当前子句，0 表示子句结束
        返回是否成功添加
        """
        # print("add_cls: ", dimacs_lit)
        if dimacs_lit == 0:
            return self._add_current_clause()
        else:
            self.current_clause.append(dimacs_lit)
            var = abs(dimacs_lit)
            if var > self.max_variable:
                self.max_variable = var
            return True
    
    def _add_current_clause(self) -> bool:
        """添加当前子句到后端"""
        self.clauses.append(self.current_clause.copy())
        if not self.current_clause:
            return False
        arr = (ctypes.c_int * len(self.current_clause))()
        for i, lit in enumerate(self.current_clause): 
            arr[i] = lit
        if self.backend == "cmsat":
            result = self.lib.cmsat_add_clause(self.solver, arr, len(self.current_clause))
        else:
            result = self.lib.minisat_add_clause(self.solver, arr, len(self.current_clause))
        self.current_clause.clear()
        return result
    
    # def _python_add_current_clause(self) -> bool:
    #     """Python 后端：添加当前子句"""
    #     if self.current_clause:
    #         self.clauses.append(self.current_clause.copy())
    #         self.current_clause.clear()
    #         return True
    #     return False
    
    def assume(self, assumption_lit: int) -> None:
        """添加假设文字"""
        self.assumptions.append(assumption_lit)
    
    def solve(self, simplify: bool = True) -> int:
        for assume in self.assumptions:
            self.pre_assumptions.append(assume)
        
        if self.backend == "cmsat":
            return self._cmsat_solve()
        else:
            return self._minisat_solve(simplify)
    
    def _cmsat_solve(self) -> int:
        """CryptoMiniSat 后端求解"""
        if self.assumptions:
            arr = (ctypes.c_int * len(self.assumptions))()
            for i, lit in enumerate(self.assumptions): 
                arr[i] = lit
            result = self.lib.cmsat_solve_with_assumptions(self.solver, arr, len(self.assumptions))
        else:
            result = self.lib.cmsat_solve(self.solver)
        self.assumptions.clear()
        
        if result == 10:
            self.solve_result = self.SAT
            self._get_model()
            self.failed_assumptions.clear()
        elif result == 20:
            self.solve_result = self.UNSAT
            self.var_values.clear()
            self._get_failed_assumptions()
        else:
            print("wrong")
            self.solve_result = self.UNKNOWN
            self.var_values.clear()
            self.failed_assumptions.clear()
        return self.solve_result
    
    def _minisat_solve(self, simplify: bool = True) -> int:
        """MiniSat 后端求解"""
        if self.assumptions:
            self.lib.minisat_clear_assumptions(self.solver)
            arr = (ctypes.c_int * len(self.assumptions))()
            for i, lit in enumerate(self.assumptions): 
                arr[i] = lit
            self.lib.minisat_set_assumptions(self.solver, arr, len(self.assumptions))
        else:
            self.lib.minisat_clear_assumptions(self.solver)
        self.assumptions.clear()
        
        result = self.lib.minisat_solve(self.solver, ctypes.c_bool(simplify))
        
        if result == 10:
            self.solve_result = self.SAT
            self._get_model()
            self.failed_assumptions.clear()
        elif result == 20:
            self.solve_result = self.UNSAT
            self.var_values.clear()
            self._get_failed_assumptions()
        else:
            print("wrong")
            self.solve_result = self.UNKNOWN
            self.var_values.clear()
            self.failed_assumptions.clear()
        return self.solve_result
    
    def _get_model(self):
        """获取模型"""
        self.var_values = {}
        if self.backend == "cmsat":
            max_var = self.lib.cmsat_max_var(self.solver)
            for var in range(1, max_var + 1):
                value = self.lib.cmsat_model_value(self.solver, var)
                if value != 0: 
                    self.var_values[var] = (value == 1)
        else:
            max_var = self.lib.minisat_max_var(self.solver)
            for var in range(1, max_var + 1):
                value = self.lib.minisat_model_value(self.solver, var - 1)
                if value != 0: 
                    self.var_values[var] = (value == 1)
    
    def _get_failed_assumptions(self):
        """获取失败假设"""
        out_size = ctypes.c_int()
        self.failed_assumptions = set()
        
        if self.backend == "cmsat":
            conflict_ptr = self.lib.cmsat_get_conflict(self.solver, ctypes.byref(out_size))
            if out_size.value > 0:
                for i in range(out_size.value):
                    lit = conflict_ptr[i]
                    self.failed_assumptions.add(-lit)
        else:
            failed_ptr = self.lib.minisat_get_failed_assumptions(self.solver, ctypes.byref(out_size))
            if out_size.value > 0:
                self.failed_assumptions = {failed_ptr[i] for i in range(out_size.value)}
    
    def val(self, lit: int) -> int:
        """
        获取文字的值
        返回: 1(真), -1(假), 0(未知)
        """
        if self.solve_result != self.SAT:
            return 0
        
        var = abs(lit)
        if var not in self.var_values:
            return 0
        
        var_value = self.var_values[var]
        if lit > 0:
            return lit if var_value else -lit
        else:
            return -lit if var_value else lit
    
    def failed(self, lit: int) -> int:
        """
        检查假设是否失败
        返回: 1(失败), 0(未失败)
        """
        if self.solve_result != self.UNSAT:
            return 0
        return 1 if lit in self.failed_assumptions else 0
    
    def max_var(self) -> int:
        """返回最大变量索引"""
        if self.backend == "cmsat":
            return self.lib.cmsat_max_var(self.solver)
        else:
            return self.lib.minisat_max_var(self.solver)
    
    def act(self) -> None:
        """清除假设和临时状态"""
        self.assumptions.clear()
        self.current_clause.clear()
        self.solve_result = self.UNKNOWN
        self.var_values.clear()
        self.failed_assumptions.clear()
           
    def clear_act(self) -> None:
        # 条件性添加约束（与 C++ 版本行为一致）
        if self.clear_flag:
            max_var = self.max_var()
            if max_var > 0:
                # 添加 [-max_var] 单文字子句
                self.add(-max_var)
                self.add(0)  # 结束子句
            self.clear_flag = False       
            
    def set_clear_act(self) -> None:
        self.clear_flag = True
    
    def add_clause(self, clause: List[int]) -> bool:
        """直接添加完整子句（备选接口）"""
        for lit in clause:
            if not self.add(lit):
                return False
        return self.add(0)  # 结束子句
    
    def add_xor_gate(self, out: int, in1: int, in2: int) -> bool:
        """添加 XOR 门: out = in1 XOR in2
        MiniSat 后端: 展开为4个CNF子句 (无原生XOR支持)
        CryptoMiniSat: 使用原生 XOR 约束
        """
        self.clauses.append([-out, in1, in2])
        self.clauses.append([-out, -in1, -in2])
        self.clauses.append([out, -in1, in2])
        self.clauses.append([out, in1, -in2])
        if self.backend == "cmsat":
            return self.lib.cmsat_add_xor_gate(self.solver, out, in1, in2)
        else:
            # MiniSat: 添加4个CNF子句
            for c in [[-out, in1, in2], [-out, -in1, -in2],
                       [out, -in1, in2], [out, in1, -in2]]:
                arr = (ctypes.c_int * len(c))(*c)
                self.lib.minisat_add_clause(self.solver, arr, len(c))
            return True

    def add_xor(self, lits) -> bool:
        """添加 XOR 约束: XOR(lits) = 0
        MiniSat 后端: 展开为CNF子句
        CryptoMiniSat: 使用原生 XOR 约束
        """
        n = len(lits)
        if n >= 2:
            if n == 3:
                self.clauses.append([-lits[0], lits[1], lits[2]])
                self.clauses.append([-lits[0], -lits[1], -lits[2]])
                self.clauses.append([lits[0], -lits[1], lits[2]])
                self.clauses.append([lits[0], lits[1], -lits[2]])
            elif n == 2:
                self.clauses.append([lits[0], lits[1]])
                self.clauses.append([-lits[0], -lits[1]])
        
        if self.backend == "cmsat":
            arr = (ctypes.c_int * n)(*lits)
            return self.lib.cmsat_add_xor_clause_lits(self.solver, arr, n, False)
        else:
            # MiniSat: 添加CNF子句
            if n == 3:
                for c in [[-lits[0], lits[1], lits[2]], [-lits[0], -lits[1], -lits[2]],
                           [lits[0], -lits[1], lits[2]], [lits[0], lits[1], -lits[2]]]:
                    arr = (ctypes.c_int * len(c))(*c)
                    self.lib.minisat_add_clause(self.solver, arr, len(c))
            elif n == 2:
                for c in [[lits[0], lits[1]], [-lits[0], -lits[1]]]:
                    arr = (ctypes.c_int * len(c))(*c)
                    self.lib.minisat_add_clause(self.solver, arr, len(c))
            return True
    
    def freeze_var(self, var: int) -> None:
        """冻结变量 (MiniSat支持, CMS忽略)"""
        if self.backend == "minisat" and hasattr(self.lib, 'minisat_freeze_var'):
            self.lib.minisat_freeze_var(self.solver, var - 1)
    
    def unfreeze_var(self, var: int) -> None:
        """解冻变量 (MiniSat支持, CMS忽略)"""
        if self.backend == "minisat" and hasattr(self.lib, 'minisat_unfreeze_var'):
            self.lib.minisat_unfreeze_var(self.solver, var - 1)
    
    def get_raw_cnf(self) -> List[int]:
        """
        获取原始 CNF 子句（MiniSat后端从C++获取, CMS从Python侧获取）
        """
        if self.backend == "minisat":
            out_size = ctypes.c_int()
            raw_cnf_ptr = self.lib.minisat_get_raw_cnf(self.solver, ctypes.byref(out_size))
            raw_cnf = []
            if out_size.value > 0:
                raw_cnf = [raw_cnf_ptr[i] for i in range(out_size.value)]
                self.lib.minisat_free_simplified_cnf(raw_cnf_ptr)
            return raw_cnf
        else:
            raw = []
            for clause in self.clauses:
                for lit in clause:
                    raw.append(lit)
                raw.append(0)
            return raw
    
    def get_clauses(self) -> List[List[int]]:
        """
        获取存储在 Python 侧的子句列表
        """
        return [clause.copy() for clause in self.clauses]
    
    def show_info(self, show_cnf: bool = False) -> None:
        """显示求解器信息"""
        print(f"SAT Solver Info:")
        print(f"  Backend: {self.backend}")
        print(f"  Max variable: {self.max_var()}")
        status_map = {self.SAT: 'SAT', self.UNSAT: 'UNSAT', self.UNKNOWN: 'Unknown'}
        print(f"  Solve result: {status_map[self.solve_result]}")
        for i, assume in enumerate(self.pre_assumptions):
            print(f"assume[{i+1}]:",assume)
        for i, clause in enumerate(self.clauses):
            print(f"clause {i}:", clause)
        if self.solve_result == self.SAT:
            print(f"  Model size: {len(self.var_values)}")
        elif self.solve_result == self.UNSAT:
            print(f"  Failed assumptions: ", self.failed_assumptions)
        self.pre_assumptions.clear()



class CubeCMP:
    """Cube 的比较器（用于 set 排序，对应 C++ 的 Cube_CMP）"""
    def __call__(self, a, b):
        # 按文字列表排序（示例逻辑，可根据实际需求修改）
        return tuple(a.literals) < tuple(b.literals)



class Frame:

    def __init__(self):
        self.cubes = set()  
        self.solver = SATSolver()

class State:
    # 移除类属性的 latches 和 inputs（类属性会被所有实例共享，此处不需要）
    index = 0
    failed = 0
    failed_depth = 0
    next = None

    def __init__(self, latches=None, inputs=None):
        global state_count 
        state_count += 1
        self.index = state_count
        # 每个实例创建独立的列表（避免共享）
        self.latches = latches.copy() if latches is not None else []
        self.inputs = inputs.copy() if inputs is not None else []
        
    def clear(self):
        self.latches.clear()  # 现在只清空当前实例的列表
        self.inputs.clear()
        self.next = None
        
class Obligation:
    # 类属性可以省略（除非需要所有实例共享默认值，这里不需要）
    def __init__(self, s, k, d):
        self.state = s       # 绑定到实例：self.xxx
        self.frame_k = k     # 绑定到实例
        self.depth = d       # 绑定到实例
    
    def __lt__(self, other):
        # 现在可以正确访问实例属性
        if self.frame_k < other.frame_k:
            return True
        if self.frame_k > other.frame_k:
            return False
        # 帧号相同时，比较深度
        return self.depth < other.depth  # 简化逻辑
    
class Log:
    def __init__(self):
        self.block_cnt = 0
        self.block_timer = 0
        self.inductive_cnt =0
        self.inductive_timer = 0
        self.min_inductive_time = 9999
        self.max_inductive_time = 0
        self.generlize_cnt = 0
        self.generlize_timer = 0
        self.ctg_cnt = 0
        self.ctg_timer = 0
        self.propagate_cnt = 0
        self.propagate_timer = 0
        self.extrct_cnt = 0
        self.extrct_timer = 0
        self.min_extract_time = 9999
        self.max_extract_time = 0
        self.prebad_cnt = 0
        self.prebad_timer = 0
        
    def _format_time(self, seconds: float) -> Tuple[str, str]:
        """辅助函数：格式化时间（自动选择秒/毫秒单位）"""
        if seconds < 0.001:
            return f"{seconds * 1000000:.2f}", "μs"
        elif seconds < 1.0:
            return f"{seconds * 1000:.2f}", "ms"
        else:
            return f"{seconds:.2f}", "s"

    def print_statistics(self):
        """打印完整统计信息：调用次数、总时间、平均时间"""
        # 定义需要统计的功能（名称 -> (计数器属性, 计时器属性)）
        stats = [
            ("Block 处理", "block_cnt", "block_timer"),
            ("inductive 操作", "inductive_cnt", "inductive_timer"),  # 保留显示，但不计入总计
            ("generlize 操作", "generlize_cnt", "generlize_timer"),
            ("CTG 处理", "ctg_cnt", "ctg_timer"),  # 保留显示，但不计入总计
            ("propagate 操作", "propagate_cnt", "propagate_timer"),
            ("extract 处理", "extrct_cnt", "extrct_timer"),  # 保留显示，但不计入总计
            ("Pre 处理", "prebad_cnt", "prebad_timer"),
        ]

        # 输出标题
        print("=" * 60)
        print(f"{'功能名称':<12} {'调用次数':<8} {'总耗时':<12} {'单次平均耗时':<12}")
        print("-" * 60)

        # 遍历每个功能，计算并输出统计
        for func_name, cnt_attr, timer_attr in stats:
            call_cnt = getattr(self, cnt_attr)
            total_time = getattr(self, timer_attr)
            
            # 格式化总时间
            total_time_str, total_unit = self._format_time(total_time)
            
            # 计算平均时间（避免除零）
            if call_cnt == 0:
                avg_time_str, avg_unit = "0.00", "ms"
            else:
                avg_time = total_time / call_cnt
                avg_time_str, avg_unit = self._format_time(avg_time)
            
            # 对齐输出
            print(f"{func_name:<12} {call_cnt:<8} {total_time_str} {total_unit:<4} {avg_time_str} {avg_unit:<4}")
        inductive_max_str, inductive_max_unit = self._format_time(self.max_inductive_time)
        inductive_min_str, inductive_min_unit = self._format_time(self.min_inductive_time)
        extract_max_str, extract_max_unit = self._format_time(self.max_extract_time)
        extract_min_str, extract_min_unit = self._format_time(self.min_extract_time)
        print(f"inductive 操作最长耗时{inductive_max_str}{inductive_max_unit},最短耗时{inductive_min_str}{inductive_min_unit}")
        print(f"extract 操作最长耗时{extract_max_str}{extract_max_unit},最短耗时{extract_min_str}{extract_min_unit}")
        excluded_timers = ["extrct_timer", "ctg_timer", "inductive_timer","generlize_timer"]
        total_all_time = 0
        for _, _, timer_attr in stats:
            if timer_attr not in excluded_timers:
                total_all_time += getattr(self, timer_attr, 0.0)
        # 输出总计信息
        print("-" * 60)
        total_calls = sum(getattr(self, cnt_attr) for _, cnt_attr, _ in stats)
        # total_all_time = sum(getattr(self, timer_attr) for _, _, timer_attr in stats)
        total_time_str, total_unit = self._format_time(total_all_time)
        print(f"{'总计':<12} {total_calls:<8} {total_time_str} {total_unit:<4} {'-':<12}")
        print("=" * 60)