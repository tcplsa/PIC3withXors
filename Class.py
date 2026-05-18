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
    
    def __init__(self):
        # MiniSat C++ 封装后端
        self.clauses = []
        self.current_clause = []
        self.assumptions = []
        self.pre_assumptions = []
        self.max_variable = 0
        self.simplified_cnf = []
        try:
            # 使用绝对路径加载（避免相对路径陷阱）
            lib_path = os.path.abspath("/home/lyj238/wdl/IC3/libminisat_wrapper.so")
            self.lib = ctypes.CDLL(lib_path)
            self._setup_lib_functions()
            self.solver = self.lib.minisat_create()
            self.backend = "minisat"
        except Exception as e:
            # 打印详细错误（如文件不存在、符号缺失等）
            print(f"初始化错误：{str(e)}")
            # 可选：如果加载失败，终止程序（避免后续错误）
            raise  # 抛出异常，停止执行
        
        # 通用常量
        self.SAT = 1
        self.UNSAT = 0
        self.UNKNOWN = -1
        
        # 状态变量
        self.solve_result = self.UNKNOWN
        self.var_values = {}
        self.failed_assumptions = []
        self.clear_flag = False
    
    def _setup_lib_functions(self):
        """设置 C++ 库函数原型"""
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
    # def _setup_python_backend(self):
    #     """设置纯 Python 后端"""
    #     self.clauses = []
    #     self.current_clause = []
    #     self.assumptions = []
    #     self.max_variable = 0
    
    def __del__(self):
        """析构函数"""
        if hasattr(self, 'solver') and self.solver and self.backend == "minisat":
            self.lib.minisat_destroy(self.solver)
    
    def simplify(self) -> List[int]:

        if self.backend != "minisat":
            print("Warning: simplify only supported for minisat backend")
            return []
        
        # 调用 C++ 后端的简化函数
        out_size = ctypes.c_int()
        simplified_ptr = self.lib.minisat_simplify(self.solver, ctypes.byref(out_size))
        
        # 将结果转换为 Python 列表
        self.simplified_cnf = []
        if out_size.value > 0:
            self.simplified_cnf = [simplified_ptr[i] for i in range(out_size.value)]
            
            # 释放 C++ 端分配的内存
            self.lib.minisat_free_simplified_cnf(simplified_ptr)
        
        return self.simplified_cnf
    
    def perform_simplify(self) -> None:
        """
        仅执行简化，不获取简化后的 CNF（性能更好）
        适用于只需要简化效果而不需要获取具体 CNF 的场景
        """
        if self.backend == "minisat":
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
        if self.backend == "minisat":
            # 调用 C++ 后端的变量扩展函数
            self.lib.minisat_var_enlarge_to(self.solver, v)
            # self.lib.minisat_var_enlarge_to(self.solver, 1000)
        
        # 更新 Python 端的最大变量记录
        if v > self.max_variable:
            self.max_variable = v
            
    def add(self, dimacs_lit: int) -> bool:
        """
        添加文字到当前子句，0 表示子句结束
        返回是否成功添加
        """
        # print("add_cls: ", dimacs_lit)
        if dimacs_lit == 0:
            


            return self._minisat_add_current_clause()
        else:
            self.current_clause.append(dimacs_lit)
            var = abs(dimacs_lit)
            if var > self.max_variable:
                self.max_variable = var
            return True
    
    def _minisat_add_current_clause(self) -> bool:
        """MiniSat 后端：添加当前子句"""
        self.clauses.append(self.current_clause.copy())
        if not self.current_clause:
            return False
            
        arr = (ctypes.c_int * len(self.current_clause))()
        for i, lit in enumerate(self.current_clause): 
            arr[i] = lit
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
        return self._minisat_solve(simplify)
    
    def _minisat_solve(self, simplify: bool = True) -> int:
        """MiniSat 后端求解"""
        # 设置假设
        if self.assumptions:
            self.lib.minisat_clear_assumptions(self.solver)
            arr = (ctypes.c_int * len(self.assumptions))()
            for i, lit in enumerate(self.assumptions): 
                arr[i] = lit
            self.lib.minisat_set_assumptions(self.solver, arr, len(self.assumptions))
        else:
            self.lib.minisat_clear_assumptions(self.solver)
        self.assumptions.clear()
        # 求解
        result = self.lib.minisat_solve(self.solver, ctypes.c_bool(simplify))
        
        if result == 10:  # SAT
            self.solve_result = self.SAT
            self._minisat_get_model()
            self.failed_assumptions.clear()
        elif result == 20:  # UNSAT
            self.solve_result = self.UNSAT
            self.var_values.clear()
            self._minisat_get_failed_assumptions()
        else:
            print("wrong")
            self.solve_result = self.UNKNOWN
            self.var_values.clear()
            self.failed_assumptions.clear()
        
        return self.solve_result
    
    def _minisat_get_model(self):
        """MiniSat 后端获取模型"""
        self.var_values = {}
        max_var = self.lib.minisat_max_var(self.solver)
        for var in range(1, max_var + 1):
            value = self.lib.minisat_model_value(self.solver, var - 1)
            if value != 0: 
                self.var_values[var] = (value == 1)
    
    def _minisat_get_failed_assumptions(self):
        """MiniSat 后端获取失败假设"""
        out_size = ctypes.c_int()
        failed_ptr = self.lib.minisat_get_failed_assumptions(self.solver, ctypes.byref(out_size))
        
        self.failed_assumptions = []
        if out_size.value > 0:
            self.failed_assumptions = {failed_ptr[i] for i in range(out_size.value)}
    
    # def _python_solve(self) -> int:
    #     """Python 后端求解（简化实现）"""
    #     # 这里应该实现一个真正的 Python SAT 求解器
    #     # 目前返回 UNKNOWN 表示需要 C++ 后端
    #     print("Warning: Python backend not fully implemented. Using MiniSat C++ backend is recommended.")
    #     self.solve_result = self.UNKNOWN
    #     self.var_values.clear()
    #     self.failed_assumptions.clear()
    #     return self.solve_result
    
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
        if self.backend == "minisat":
            return self.lib.minisat_max_var(self.solver)
        else:
            return self.max_variable
    
    def act(self) -> None:
        """清除假设和临时状态"""
        self.assumptions.clear()
        self.current_clause.clear()
        self.solve_result = self.UNKNOWN
        self.var_values.clear()
        self.failed_assumptions.clear()
        
        if self.backend == "minisat":
            self.lib.minisat_clear_assumptions(self.solver)
           
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
    
    # 可选的高级功能
    def freeze_var(self, var: int) -> None:
        """冻结变量（仅 MiniSat 后端支持）"""
        if self.backend == "minisat" and hasattr(self.lib, 'minisat_freeze_var'):
            self.lib.minisat_freeze_var(self.solver, var - 1)
    
    def unfreeze_var(self, var: int) -> None:
        """解冻变量（仅 MiniSat 后端支持）"""
        if self.backend == "minisat" and hasattr(self.lib, 'minisat_unfreeze_var'):
            self.lib.minisat_unfreeze_var(self.solver, var - 1)
    
    
    def get_raw_cnf(self) -> List[int]:
        """
        获取原始 CNF 子句（不执行简化）
        返回格式与 simplify() 相同，但不执行实际的简化操作
        """
        if self.backend != "minisat":
            return []
        
        out_size = ctypes.c_int()
        raw_cnf_ptr = self.lib.minisat_get_raw_cnf(self.solver, ctypes.byref(out_size))
        
        raw_cnf = []
        if out_size.value > 0:
            raw_cnf = [raw_cnf_ptr[i] for i in range(out_size.value)]
            
            # 释放 C++ 端分配的内存
            self.lib.minisat_free_simplified_cnf(raw_cnf_ptr)
        
        return raw_cnf
    
    def show_raw_cnf(self) -> None:
        """以可读格式显示原始 CNF"""
        raw_cnf = self.get_raw_cnf()
        if not raw_cnf:
            print("No raw CNF available.")
            return
        
        print("Raw CNF (without simplification):")
        clause = []
        clause_num = 1
        for lit in raw_cnf:
            if lit == 0:
                if clause:
                    # 跳过变量数量信息行 (nVars, -nVars, 0)
                    if len(clause) == 3 and clause[0] > 0 and clause[1] == -clause[0] and clause[2] == 0:
                        print(f"  Variables: {clause[0]}")
                    else:
                        print(f"  Clause {clause_num}: {' '.join(str(l) for l in clause)}")
                        clause_num += 1
                    clause = []
            else:
                clause.append(lit)
        
        # 打印最后一个子句（如果有）
        if clause:
            print(f"  Clause {clause_num}: {' '.join(str(l) for l in clause)}")
    
    def get_clauses(self) -> List[List[int]]:
        """
        获取原始 CNF 子句列表
        返回: 子句列表，每个子句是一个文字列表
        """
        raw_cnf = self.get_raw_cnf()
        clauses = []
        current_clause = []
        
        for lit in raw_cnf:
            if lit == 0:
                if current_clause:
                    # 跳过变量数量信息行 (nVars, -nVars, 0)
                    if len(current_clause) != 3 or not (current_clause[0] > 0 and current_clause[1] == -current_clause[0] and current_clause[2] == 0):
                        clauses.append(current_clause.copy())
                    current_clause.clear()
            else:
                current_clause.append(lit)
        
        # 添加最后一个子句（如果有）
        if current_clause:
            clauses.append(current_clause)
        
        return clauses
    
    def show_info(self, show_cnf: bool = False) -> None:
        """显示求解器信息"""
        print(f"SAT Solver Info:")
        print(f"  Backend: {self.backend}")
        print(f"  Max variable: {self.max_var()}")
        status_map = {self.SAT: 'SAT', self.UNSAT: 'UNSAT', self.UNKNOWN: 'Unknown'}
        print(f"  Solve result: {status_map[self.solve_result]}")
        for i, assume in enumerate(self.pre_assumptions):
            print(f"assume[{i+1}]:",assume)
        # for i, clause in enumerate(self.clauses):
        #     print(f"clause {i}:", clause)
        raw_clauses = self.get_clauses()
        # with open("raw_clauses.txt", "w") as f:
        #     for i, clause in enumerate(raw_clauses):
        #         f.write(f"clause {i}: {' '.join(map(str, clause))}\n")
                
        # with open("clauses.txt", "w") as f:
        #     for i, clause in enumerate(self.clauses):
        #         f.write(f"clause {i}: {' '.join(map(str, clause))}\n")        
        # for i, clause in enumerate(raw_clauses):
        #     print(f"clause {i}:", clause)
            
        for i, clause in enumerate(self.clauses):
            print(f"clause {i}:", clause)
        
        if show_cnf:
            raw_clauses = self.get_clauses()
            for i, clause in enumerate(raw_clauses):
                print(f"raw clause {i}:", clause)
        if self.solve_result == self.SAT:
            print(f"  Model size: {len(self.var_values)}")
        elif self.solve_result == self.UNSAT:
            print(f"  Failed assumptions: ", self.failed_assumptions)
        # print(self.var_values)
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