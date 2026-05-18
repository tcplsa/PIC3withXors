
from Class import *
from functools import cmp_to_key
import random
import sys
import time
# from readblif import parse_blif_with_continuous_vars

frames = []
states = []
use_heuristic = 0
bad = 0
bad_prime = 0
obligation_queue = []
core = []
map_to_prime = []
init_state = []
nexts = []
num_inputs = 0
num_latches = 0
num_constraints = 0
num_ands = 0
num_xors = 0   
num_ors = 0

nkobl = 0
earliest_strengthened_frame = 0
top_frame_cannot_reach_bad = True
unprimed_first_dimacs = 2
primed_first_dimacs = 0
variables = []
inputs = []
ands = []
xors = []
ors = []
latches = []
unknown = False
constraints_prime = []
constraints = []
lift = None
init = None
satelite1 = None
satelite2 = None
# CTG / generalization options (defaults if not configured elsewhere)
option_ctg_tries = 5
option_ctg_max_depth = 0
option_max_joins = 1<<20
output_stats_for_ctg = False

log = Log()

show_propagate_info = True
show_block_info = True
show_pre_of_bad = False

# show_propagate_info = False
# show_block_info = False
# show_pre_of_bad = False


def depth():
    return len(frames) - 2



    
def prime_var(var: int) -> int:
    if not hasattr(prime_var, "map_to_prime"):
        prime_var.map_to_prime = {} 
    if not hasattr(prime_var, "map_to_unprime"):
        prime_var.map_to_unprime = {} 

    assert var != 1, f"变量{var}必须≥1"
    
    if var > 1:
        if var not in prime_var.map_to_prime:
            unprimed_var = var
            while len(variables) <= unprimed_var:
                variables.append(Variable(len(variables), f"unknown_{len(variables)}"))
            for i,v in enumerate(variables):
                if abs(v.dimacs_var) == unprimed_var:
                    id = i
                    break
            try:
                new_name = f"{variables[id].name}'"
            except:
                new_name = f"var{unprimed_var}'"
                print(f"Warning: variable {unprimed_var} not found in variables list, using default name {new_name}")
            primed_var = len(variables)
            prime_var.map_to_prime[unprimed_var] = primed_var
            prime_var.map_to_unprime[primed_var] = unprimed_var
            variables.append(Variable(primed_var, new_name)) 
            
        return prime_var.map_to_prime[var]
    else:
        return var

def prime_lit(lit):
    if lit >= 0:
        return prime_var(lit)
    else:
        return -prime_var(-lit)

def show_state(s):
    # 初始化字符列表，长度为输入数+锁存器数+2，默认值'x'
    a = ['x'] * (num_inputs + num_latches + 200)

    # 处理输入（inputs）：根据符号设置 '0' 或 '1'
    for i in s.inputs:
        abs_i = abs(i)
        a[abs_i] = '0' if i < 0 else '1'
    
    # 处理锁存器（latches）：根据符号设置 '0' 或 '1'
    for l in s.latches:
        abs_l = abs(l)
        a[abs_l] = '0' if l < 0 else '1'
    
    # 构建并打印输出字符串
    output = '['
    # 添加输入部分（索引 1+1 到 1+num_inputs）
    for i in range(1, num_inputs + 1):
        output += a[1 + i]
    # 添加分隔符
    output += '|'
    # 添加锁存器部分（索引 1+num_inputs+1 到 1+num_inputs+num_latches）
    for l in range(1, num_latches + 1):
        output += a[1 + num_inputs + l]
    output += ']'
    
    print(output)



def encode_lift(s):
    global blif
    global satelite2
    satelite_unsat = False
    if satelite2 == None:
        satelite2 = SATSolver()
        satelite2.var_enlarge_to(len(variables)-1)
        for i in blif.inputs:
            satelite2.freeze_var(i)
            satelite2.freeze_var(prime_var(i))
        for l in blif.latches:
            satelite2.freeze_var(abs(l[1]))
            satelite2.freeze_var(prime_var(abs(l[1])))
        satelite2.freeze_var(abs(bad))
        satelite2.freeze_var(abs(bad_prime))
        
        for i in range(0, num_constraints):
            satelite2.freeze_var(abs(constraints[i]))
            satelite2.freeze_var(prime_var(abs(constraints[i])))
        
        prime_lit_set = set()
        prime_lit_set.add(abs(bad))
        for l in constraints:
            prime_lit_set.add(abs(l))
        lit_set = prime_lit_set.copy()
        for l in nexts:
            lit_set.add(abs(l))
        satelite2.add(-1)
        satelite2.add(0)
        # print(-bad)
        satelite2.add(-bad)
        satelite2.add(0)
        for i in blif.latches:
            l = i[1]
            pl = prime_lit(l)
            next = i[0]
            # print("pl: ",pl," next: ",next)
            satelite2.add(-pl)
            satelite2.add(next)
            satelite2.add(0)
            satelite2.add(-next)
            satelite2.add(pl)
            satelite2.add(0)
        #print(lit_set)
        gates = ands + xors + ors
        gates.sort(key=lambda x: x[0])  # 按输出变量升序排序
        # print("gates: ", gates)
        for g in reversed(gates):
            if g in ands:
                assert g[0] > 0, f"And门输出g[0]必须为正数，实际为{g[0]}"
                if g[0] in lit_set:
                    lit_set.add(abs(g[1]))
                    lit_set.add(abs(g[2]))
                    # print("g[0]: ",g[0]," g[1]: ",g[1]," g[2]: ",g[2])
                    satelite2.add(-g[0])
                    satelite2.add(g[1])
                    satelite2.add(0)  
                    satelite2.add(-g[0])
                    satelite2.add(g[2])
                    satelite2.add(0) 
                    satelite2.add(g[0])
                    satelite2.add(-g[1])
                    satelite2.add(-g[2])
                    satelite2.add(0)
                    if g[0] in prime_lit_set:
                        po = prime_lit(g[0])
                        pi1 = prime_lit(g[1])
                        pi2 = prime_lit(g[2])
                        # print("po: ",po," pi1: ",pi1," pi2: ",pi2)
                        prime_lit_set.add(abs(g[1]))
                        prime_lit_set.add(abs(g[2]))
                        
                        satelite2.add(-po)
                        satelite2.add(pi1)
                        satelite2.add(0)  
                        
                        satelite2.add(-po)
                        satelite2.add(pi2)
                        satelite2.add(0) 
                        
                        satelite2.add(po)
                        satelite2.add(-pi1)
                        satelite2.add(-pi2)
                        satelite2.add(0) 
        
            if g in xors:
                assert g[0] > 0, f"Xor门输出g[0]必须为正数，实际为{g[0]}"
                if g[0] in lit_set:
                    lit_set.add(abs(g[1]))
                    lit_set.add(abs(g[2]))
                    # print("g[0]: ",g[0]," g[1]: ",g[1]," g[2]: ",g[2])
                    satelite2.add(-g[0])
                    satelite2.add(g[1])
                    satelite2.add(g[2])
                    satelite2.add(0)  
                    satelite2.add(-g[0])
                    satelite2.add(-g[1])
                    satelite2.add(-g[2])
                    satelite2.add(0) 
                    satelite2.add(g[0])
                    satelite2.add(-g[1])
                    satelite2.add(g[2])
                    satelite2.add(0)  
                    
                    satelite2.add(g[0])
                    satelite2.add(g[1])
                    satelite2.add(-g[2])
                    satelite2.add(0) 
                    
                    if g[0] in prime_lit_set:
                        po = prime_lit(g[0])
                        pi1 = prime_lit(g[1])
                        pi2 = prime_lit(g[2])
                        
                        prime_lit_set.add(abs(g[1]))
                        prime_lit_set.add(abs(g[2]))
                        # print("po: ",po," pi1: ",pi1," pi2: ",pi2)
                        satelite2.add(-po)
                        satelite2.add(pi1)
                        satelite2.add(pi2)
                        satelite2.add(0)  
                        
                        satelite2.add(-po)
                        satelite2.add(-pi1)
                        satelite2.add(-pi2)
                        satelite2.add(0) 
                        
                        satelite2.add(po)
                        satelite2.add(pi1)
                        satelite2.add(-pi2)
                        satelite2.add(0)
                        
                        satelite2.add(po)
                        satelite2.add(-pi1)
                        satelite2.add(pi2)
                        satelite2.add(0)
        
            if g in ors:
                assert g[0] > 0, f"Or门输出g[0]必须为正数，实际为{g[0]}"
                if g[0] in lit_set:
                    lit_set.add(abs(g[1]))
                    lit_set.add(abs(g[2]))
                    # o = i1 | i2
                    # (o → i1∨i2): ~o ∨ i1 ∨ i2
                    satelite2.add(-g[0])
                    satelite2.add(g[1])
                    satelite2.add(g[2])
                    satelite2.add(0)
                    # (i1 → o): o ∨ ~i1
                    satelite2.add(g[0])
                    satelite2.add(-g[1])
                    satelite2.add(0)
                    # (i2 → o): o ∨ ~i2
                    satelite2.add(g[0])
                    satelite2.add(-g[2])
                    satelite2.add(0)
                    if g[0] in prime_lit_set:
                        po = prime_lit(g[0])
                        pi1 = prime_lit(g[1])
                        pi2 = prime_lit(g[2])
                        prime_lit_set.add(abs(g[1]))
                        prime_lit_set.add(abs(g[2]))
                        # (~po ∨ pi1 ∨ pi2)
                        satelite2.add(-po)
                        satelite2.add(pi1)
                        satelite2.add(pi2)
                        satelite2.add(0)
                        # (po ∨ ~pi1)
                        satelite2.add(po)
                        satelite2.add(-pi1)
                        satelite2.add(0)
                        # (po ∨ ~pi2)
                        satelite2.add(po)
                        satelite2.add(-pi2)
                        satelite2.add(0)
        # satelite.show_info()
        satelite2.simplify()
        # satelite.show_info()
        # exit(0)
    # clauses = satelite2.get_clauses()
    # for c in clauses:
    #     for l in c:
    #         s.add(l)
    #     s.add(0)
    for l in satelite2.simplified_cnf:
        s.add(l)
    if satelite_unsat == True:
        s.add(1)
        s.add(0)
    # print("add_cls finish load transition")
    # exit(0)
    return satelite2

def extract_state_from_sat(sat, s, succ, index):
    print("extract_state_from_sat")
    log.extrct_cnt += 1
    start_time = time.perf_counter()
    global lift
    s.clear()
    if lift == None:
        lift = SATSolver()
        encode_lift(lift)
    print("constraints: ", constraints)
    print("constraints_prime: ", constraints_prime)
    for l in constraints:
        lift.add(l)
        lift.add(0)
    for l in constraints_prime:
        lift.add(l)
        lift.add(0)
    # print("clear_flag",lift.clear_flag)
    lift.clear_act()
    # print("lift")
    # lift.show_info()
    assumptions = []
    elatches = []
    distance = primed_first_dimacs - ( num_inputs + num_latches + 2 )
    for i in range (0, num_inputs):
        ipt = sat.val(inputs[i])
        pipt = sat.val(prime_lit(inputs[i]))
        if ipt != 0:
            s.inputs.append(ipt)
            assumptions.append(ipt)
        if pipt > 0:
            # pipt = pipt - distance
            assumptions.append(pipt)
        elif pipt < 0:
            # pipt = -(-pipt - distance)
            assumptions.append(pipt)
    
    sz = len(assumptions)
    for i in range(0, num_latches):
        l = sat.val(latches[i])
        if l != 0:
            elatches.append(l)
            assumptions.append(l)
    
    act_var = lift.max_var() + 1
    print("act_var", act_var)
    
    lift.add(-act_var)


            
    if succ == None:
        lift.add(-bad_prime)
    else:
        for l in succ.latches: 
            lift.add(prime_lit(-l))
    lift.add(0)
    # print("lift add")
    
    
    assumptions.sort(key=cmp_to_key(lit_cmp))
    # for i in range(0, len(assumptions)):
    #     if assumptions[i] >= num_inputs + num_latches + 2:
    #         assumptions[i] = assumptions[i] + distance
    #     elif assumptions[i] <= - (num_inputs + num_latches + 2):
    #         assumptions[i] = assumptions[i] - distance
            
    lift.assume(act_var)
    for l in assumptions:
        # print("assume: ", l)
        lift.assume(l)

    res = lift.solve(False)
    # lift.show_info()
    for c in range(0,lift.max_var()+1):
        # print("c: ",lift.val(c))
        pass
    assert res == 0, f"不应为SAT"
    # print("lift:")
    for l in assumptions:
        if lift.failed(l):
            pass
            # print(variables[abs(l)].name)
    
    for l in elatches:
        if lift.failed(l):
            s.latches.append(l)
    '''
    corelen = 0
    last_index = 0
    for i in range(0, len(assumptions)):
        l = assumptions[i]
        if abs(l) >= num_inputs + 2 and abs(l) <= num_inputs + num_latches + 1:
            corelen += 1
        if lift.failed(l):
            last_index = corelen
    '''
    s.next = succ
    lift.set_clear_act()
    end_time = time.perf_counter()
    log.extrct_timer += (end_time - start_time)
    if end_time - start_time > log.max_extract_time:
        log.max_extract_time = end_time - start_time
    if end_time - start_time < log.min_extract_time:
        log.min_extract_time = end_time - start_time
    return

def get_pre_of_bad(s):
    log.prebad_cnt += 1
    start_time = time.perf_counter()
    global show_pre_of_bad
    if show_pre_of_bad:
        print("get pre of bad")
    global bad_prime
    s.clear()
    Fk = depth()
    if show_pre_of_bad:
        print("Fk=",Fk)
    # res = frames[Fk].solver.solve()
    # print("res before:",res)
    frames[Fk].solver.assume(bad_prime)
    # frames[Fk].solver.show_info()
    res = frames[Fk].solver.solve(False)
    
    # frames[Fk].solver.show_info()
    
    for c in range(0,frames[Fk].solver.max_var()+1):
        # print("c: ",frames[Fk].solver.val(c))
        pass
    # res = 0
    print("res:",res)
    SAT = 1
    if res == SAT:  
        # sys.exit()
        bad_state = State()  

        for i in range(0, num_inputs):
            pipt = frames[Fk].solver.val(prime_var(abs(inputs[i])))
            # print("pipt: ", pipt)
            if pipt > 0:
                bad_state.inputs.append(abs(inputs[i]))
                # print("pipt add = ",abs(inputs[i]))
            elif pipt < 0:
                bad_state.inputs.append(-abs(inputs[i]))
                # print("pipt add = ",-abs(inputs[i]))
        

        for i in range(0, num_latches):
            l_val = frames[Fk].solver.val(prime_var(abs(latches[i])))
            # print("l_val: ", l_val)
            if l_val > 0:
                bad_state.latches.append(abs(latches[i]))
                # print("l add = ",abs(latches[i]))
            elif l_val < 0:
                bad_state.latches.append(-abs(latches[i]))
                # print("l add = ",-abs(latches[i]))
        extract_state_from_sat(frames[Fk].solver, s, None, Fk)  
        s.next = bad_state
        # print(s.next.latches) 
        if show_pre_of_bad:
            show_state(s)
            pass 
        end_time = time.perf_counter()
        log.prebad_timer += (end_time - start_time)
        return True
    else:  
        end_time = time.perf_counter()
        log.prebad_timer += (end_time - start_time)
        return False
    
def encode_init_condition(s):
    global blif
    s.add(-1)
    s.add(0)
    for l in blif.latches:
        if l[2] == 1:
            s.add(int(l[1]))
            s.add(0)
        elif l[2] == 0:
            s.add(int(-l[1]))
            s.add(0)

    if 0 >= 0:
        for l in blif.constraints:
            s.add((l))
            s.add(0)

        lit_set = set()
        for l in blif.constraints:
            lit_set.add(abs(l))

        gates = ands + xors + ors
        gates.sort(key=lambda x: x[0])
        for g in reversed(gates):
            if g in ands:
                assert g[0] > 0, f"And门输出g[0]必须为正数，实际为{g[0]}"
                if g[0] in lit_set:
                    lit_set.add(abs(g[1]))
                    lit_set.add(abs(g[2]))
                    s.add(-g[0])
                    s.add(g[1])
                    s.add(0)  
                    s.add(-g[0])
                    s.add(g[2])
                    s.add(0) 
                    s.add(g[0])
                    s.add(-g[1])
                    s.add(-g[2])
                    s.add(0)
            if g in xors:
                assert g[0] > 0, f"Xor门输出g[0]必须为正数，实际为{g[0]}"
                if g[0] in lit_set:
                    lit_set.add(abs(g[1]))
                    lit_set.add(abs(g[2]))
                    s.add(-g[0])
                    s.add(g[1])
                    s.add(g[2])
                    s.add(0)  
                    s.add(-g[0])
                    s.add(-g[1])
                    s.add(-g[2])
                    s.add(0) 
                    s.add(g[0])
                    s.add(-g[1])
                    s.add(g[2])
                    s.add(0)  
                    
                    s.add(g[0])
                    s.add(g[1])
                    s.add(-g[2])
                    s.add(0)
            if g in ors:
                assert g[0] > 0, f"Or门输出g[0]必须为正数，实际为{g[0]}"
                if g[0] in lit_set:
                    lit_set.add(abs(g[1]))
                    lit_set.add(abs(g[2]))
                    s.add(-g[0])
                    s.add(g[1])
                    s.add(0)  
                    s.add(-g[0])
                    s.add(g[2])
                    s.add(0) 
                    s.add(-g[0])
                    s.add(g[1])
                    s.add(g[2])
                    s.add(0)
        
        # for a in reversed(blif.ands):
        #     if a[0] not in lit_set:
        #         continue
        #     lit_set.add(abs(a[1]))
        #     lit_set.add(abs(a[2]))

        #     s.add((-a[0]))
        #     s.add((a[1]))
        #     s.add(0)
            
        #     s.add((-a[0]))
        #     s.add((a[2]))
        #     s.add(0)
            
        #     s.add((a[0]))
        #     s.add((-a[1]))
        #     s.add((-a[2]))
        #     s.add(0)
            
        # for x in reversed(blif.xors):
        #     if x[0] not in lit_set:
        #         continue
        #     lit_set.add(abs(x[1]))
        #     lit_set.add(abs(x[2]))

        #     s.add((-x[0]))
        #     s.add((x[1]))
        #     s.add((x[2]))
        #     s.add(0)
            
        #     s.add((-x[0]))
        #     s.add((-x[1]))
        #     s.add((-x[2]))
        #     s.add(0)
            
        #     s.add((x[0]))
        #     s.add((-x[1]))
        #     s.add((x[2]))
        #     s.add(0)
            
        #     s.add((x[0]))
        #     s.add((x[1]))
        #     s.add((-x[2]))
        #     s.add(0)
    return s
    # print("add_cls finish load init")

def is_init(latches):
    global init
    if init == None:
        init = SATSolver()
        init = encode_init_condition(init)
    for l in latches:
        init.assume(l)
    res = init.solve()
    assert res != -1
    return res == 1
    
    
def encode_translation(s,satelite,cons = True):
    global blif
    satelite_unsat = False
    if satelite == None:
        satelite = SATSolver()
        satelite.var_enlarge_to(len(variables)-1)
        for i in blif.inputs: 
            satelite.freeze_var(abs(i))
            satelite.freeze_var(prime_var(abs(i)))
        for l in blif.latches:
            satelite.freeze_var(abs(l[1]))
            satelite.freeze_var(prime_var(abs(l[1])))
        satelite.freeze_var(abs(bad))
        satelite.freeze_var(abs(bad_prime))
        
        for i in range(0, num_constraints):
            satelite.freeze_var(abs(constraints[i]))
            satelite.freeze_var(prime_var(abs(constraints[i])))
        
        prime_lit_set = set()
        prime_lit_set.add(abs(bad))
        for l in constraints:
            prime_lit_set.add(abs(l))
        lit_set = prime_lit_set.copy()
        for l in nexts:
            lit_set.add(abs(l))
        print(lit_set)
        satelite.add(-1)
        satelite.add(0)
        print(-bad)
        satelite.add(-bad)
        satelite.add(0)
        if cons == True:
            for l in constraints:
                if l == bad:
                    satelite_unsat = True
                satelite.add((l))
                satelite.add(0)
            # for l in constraints_prime:
            #     satelite.add((l))
            #     satelite.add(0)
        for i in blif.latches:
            l = i[1]
            pl = prime_lit(l)
            next = i[0]
            # print("pl: ",pl," next: ",next)
            satelite.add(-pl)
            satelite.add(next)
            satelite.add(0)
            satelite.add(-next)
            satelite.add(pl)
            satelite.add(0)
        # print(lit_set)
        gates = ands + xors + ors
        gates.sort(key=lambda x: x[0])  # 按输出变量升序排序
        # print("gates: ", gates)
        for g in reversed(gates):
            # print(g)
            if g in ands:
                assert g[0] > 0, f"And门输出g[0]必须为正数，实际为{g[0]}"
                if g[0] in lit_set:
                    lit_set.add(abs(g[1]))
                    lit_set.add(abs(g[2]))
                    # print("g[0]: ",g[0]," g[1]: ",g[1]," g[2]: ",g[2])
                    satelite.add(-g[0])
                    satelite.add(g[1])
                    satelite.add(0)  
                    satelite.add(-g[0])
                    satelite.add(g[2])
                    satelite.add(0) 
                    satelite.add(g[0])
                    satelite.add(-g[1])
                    satelite.add(-g[2])
                    satelite.add(0)
                    if g[0] in prime_lit_set:
                        po = prime_lit(g[0])
                        pi1 = prime_lit(g[1])
                        pi2 = prime_lit(g[2])
                        prime_lit_set.add(abs(g[1]))
                        prime_lit_set.add(abs(g[2]))
                        satelite.add(-po)
                        satelite.add(pi1)
                        satelite.add(0)  
                        
                        satelite.add(-po)
                        satelite.add(pi2)
                        satelite.add(0) 
                        
                        satelite.add(po)
                        satelite.add(-pi1)
                        satelite.add(-pi2)
                        satelite.add(0) 
        
            if g in xors:
                assert g[0] > 0, f"Xor门输出g[0]必须为正数，实际为{g[0]}"
                if g[0] in lit_set:
                    lit_set.add(abs(g[1]))
                    lit_set.add(abs(g[2]))
                    # print("g[0]: ",g[0]," g[1]: ",g[1]," g[2]: ",g[2])
                    satelite.add(-g[0])
                    satelite.add(g[1])
                    satelite.add(g[2])
                    satelite.add(0)  
                    satelite.add(-g[0])
                    satelite.add(-g[1])
                    satelite.add(-g[2])
                    satelite.add(0) 
                    satelite.add(g[0])
                    satelite.add(-g[1])
                    satelite.add(g[2])
                    satelite.add(0)  
                    
                    satelite.add(g[0])
                    satelite.add(g[1])
                    satelite.add(-g[2])
                    satelite.add(0) 
                    
                    if g[0] in prime_lit_set:
                        po = prime_lit(g[0])
                        pi1 = prime_lit(g[1])
                        pi2 = prime_lit(g[2])
                        prime_lit_set.add(abs(g[1]))
                        prime_lit_set.add(abs(g[2]))
                        # print("po: ",po," pi1: ",pi1," pi2: ",pi2)
                        satelite.add(-po)
                        satelite.add(pi1)
                        satelite.add(pi2)
                        satelite.add(0)  
                        
                        satelite.add(-po)
                        satelite.add(-pi1)
                        satelite.add(-pi2)
                        satelite.add(0) 
                        
                        satelite.add(po)
                        satelite.add(pi1)
                        satelite.add(-pi2)
                        satelite.add(0)
                        
                        satelite.add(po)
                        satelite.add(-pi1)
                        satelite.add(pi2)
                        satelite.add(0)
            if g in ors:
                assert g[0] > 0, f"Or门输出g[0]必须为正数，实际为{g[0]}"
                if g[0] in lit_set:
                    lit_set.add(abs(g[1]))
                    lit_set.add(abs(g[2]))
                    # print("g[0]: ",g[0]," g[1]: ",g[1]," g[2]: ",g[2])
                    satelite.add(-g[0])
                    satelite.add(g[1])
                    satelite.add(g[2])
                    satelite.add(0)
                      
                    satelite.add(g[0])
                    satelite.add(-g[1])
                    satelite.add(0)  
                    
                    satelite.add(g[0])
                    satelite.add(-g[2])
                    satelite.add(0) 
                    
                    if g[0] in prime_lit_set:
                        po = prime_lit(g[0])
                        pi1 = prime_lit(g[1])
                        pi2 = prime_lit(g[2])
                        prime_lit_set.add(abs(g[1]))
                        prime_lit_set.add(abs(g[2]))
                        # print("po: ",po," pi1: ",pi1," pi2: ",pi2)
                        satelite.add(-po)
                        satelite.add(pi1)
                        satelite.add(pi2)
                        satelite.add(0)  
                        
                        satelite.add(po)
                        satelite.add(-pi1)
                        satelite.add(0)  
                        
                        satelite.add(po)
                        satelite.add(-pi2)
                        satelite.add(0)
        # satelite.show_info()
        satelite.simplify()
        # satelite.show_info()
        # exit(0)
    # clauses = satelite.get_clauses()
    # for c in clauses:
    #     for l in c:
    #         s.add(l)
    #     s.add(0)
    for l in satelite.simplified_cnf:
        s.add(l)
    if satelite_unsat == True:
        s.add(1)
        s.add(0)
    # s.show_info()
    # for v in variables:
    #     print(f"变量{v.dimacs_var} ({v.name})")
    # print("add_cls finish load transition")
    # exit(0)
    return satelite
    
    
def lit_cmp(a: int, b: int) -> int:
    abs_a = abs(a)
    abs_b = abs(b)
    if abs_a < abs_b:
        return -1  # a排在b前
    elif abs_a > abs_b:
        return 1   # b排在a前
    else:
        # 绝对值相等时，按数值本身从小到大排
        return -1 if a < b else 1 if a > b else 0

def is_inductive(solver, latches, gen_core = False, reverse_assumption = False):
    log.inductive_cnt += 1
    start_time = time.perf_counter()
    # print("start is_inductive")
    global core
    solver.clear_act()
    assumptions = []
    act = solver.max_var() + 1
    solver.add((-act))
    for i in latches:
        solver.add((-i))
    solver.add(0)
    if use_heuristic == 1:
        pass
    else:
        for i in latches:
            assumptions.append(prime_lit(i))
        assumptions.sort(key=cmp_to_key(lit_cmp))
    
    solver.assume(act)
    for i in assumptions:
        solver.assume(i)
    status = solver.solve(False)
    
    res = (status == 0)
    if res == True and gen_core == True:
        core.clear()
        for i in latches:
            if solver.failed(prime_lit(i)):
                core.append(i)
        if is_init(core):
            core[:] = list(latches)

    solver.set_clear_act()
    # print("core: ",core)
    # print("end is_inductive")
    end_time = time.perf_counter()
    log.inductive_timer += (end_time - start_time)
    if end_time - start_time > log.max_inductive_time:
        log.max_inductive_time = end_time - start_time
    if end_time - start_time < log.min_inductive_time:
        log.min_inductive_time = end_time - start_time
    return res



def generalize(cube, k, depth):
    log.generlize_cnt += 1
    start_time = time.perf_counter()
    mic_failed = 0
    required = []
    cube.sort(key = lambda x:(abs(x),x))
    random.shuffle(cube)
    
    tmp_cube = list(cube)
    for l in tmp_cube:
        cand = []
        if l not in cube:
           mic_failed = 0
           continue
        for i in cube:
            if i != l:
                cand.append(i)
        
        if CTG_down(cand, k, depth, required):
            mic_failed = 0
            # update the original list in-place so the caller sees the change
            cube[:] = cand
        else:
            mic_failed += 1
            if mic_failed > option_ctg_tries:
                break
            required.append(l)
    end_time = time.perf_counter()
    log.generlize_timer += (end_time - start_time)
    return

def CTG_down(cube, k, rec_depth, required):
    # Implements CTG_down behavior ported from the provided C++ version.
    # cube: list of literals
    # k: frame index
    # rec_depth: recursion depth
    # required: list of literals that must be kept
    # aig: optional AIG structure (passed from callers); required for is_init checks
    log.ctg_cnt += 1
    start_time = time.perf_counter()
    global option_ctg_max_depth, option_ctg_tries, option_max_joins

    # if aig is None:
    #     # best-effort: try to use a name 'aig' from caller scope if set as global
    #     try:
    #         aig = globals().get('aig', None)
    #     except Exception:
    #         aig = None

    ctg_ct = 0
    join_ct = 0
    while True:
        # if cube is reachable from init, cannot CTG
        if  is_init(cube):
            end_time = time.perf_counter()
            log.ctg_timer += (end_time - start_time)
            return False

        # check inductive at this frame
        sat = frames[k].solver
        if is_inductive(sat, cube, True):
            if output_stats_for_ctg:
                print("The new cube satisfies induction")
            # if core is smaller, replace
            try:
                if len(core) < len(cube):
                    cube[:] = core[:]  # replace contents
            except Exception:
                pass
            end_time = time.perf_counter()
            log.ctg_timer += (end_time - start_time)
            return True
        else:
            # depth guard
            if rec_depth > option_ctg_max_depth:
                end_time = time.perf_counter()
                log.ctg_timer += (end_time - start_time)
                return False

            # get counterexample / successor state
            s = State()
            succ = State()
            # make succ.latches contain the current cube (matches C++: State(cube, Cube()))
            try:
                succ.latches = list(cube)
            except Exception:
                succ.latches = []
            # succ.next isn't used here in Python version; match C++'s extract call
            extract_state_from_sat(sat, s, succ, k)

            breaked = False
            # attempt CTG lifting if allowed
            if (ctg_ct < option_ctg_tries and k > 1
                    and (not is_init(s.latches))
                    and is_inductive(frames[k-1].solver, s.latches, True)):
                if output_stats_for_ctg:
                    print("ctg satisfies induction, is lifted to", core)

                # use current core as ctg (reference to global core, like C++ Cube &ctg = core)
                ctg = core
                ctg_ct += 1
                # try to push ctg forward
                i = k
                for i in range(k, depth() + 1):
                    # increment push attempts counter optional
                    if not is_inductive(frames[i].solver, ctg, False):
                        break
                Size = len(ctg)
                # recursively minimize / generalize ctg
                # call generalize/mic: we pass aig so is_init checks work
                generalize(ctg, i-1, rec_depth+1)
                add_cube(ctg, i, True, False, i - k + 1 + (1 if len(ctg) < Size else 0))
            else:
                # join attempt
                if join_ct < option_max_joins:
                    ctg_ct = 0
                    join_ct += 1
                    join = []
                    s_cti = set(s.latches)
                    for lit in cube:
                        if lit in s_cti:
                            join.append(lit)
                        elif lit in required:
                            breaked = True
                            # nAbortJoin counter not present; ignore
                            break
                    # replace cube contents
                    cube[:] = join
                    if output_stats_for_ctg:
                        print("breaked =", breaked, ", ctg cant be removed, join cube and ctg", cube)
                else:
                    breaked = True

            # cleanup (in C++ delete s, succ)
            if breaked:
                end_time = time.perf_counter()
                log.ctg_timer += (end_time - start_time)
                return False




def add_cube(cube, k ,to_all, ispropagate, prtimes):
    global earliest_strengthened_frame
    if ispropagate == False:
        earliest_strengthened_frame =min(earliest_strengthened_frame,k)
    cube.sort(key = lambda x:(abs(x),x))
    cube_tuple = tuple(cube)
    if cube_tuple in frames[k].cubes:
        return
    frames[k].cubes.add(cube_tuple)
    # print("Added cube(sz",len(cube),") to frame", k, ":")
    # for c in cube:
    #     print("-" if c < 0 else "", variables[abs(c)].name, end=' ')
    # print()
    if to_all == True:
        for i in range(1, k):
            for l in cube:
                frames[i].solver.add((-l))
            frames[i].solver.add(0)
    for l in cube:
        frames[k].solver.add((-l))
    frames[k].solver.add(0)
    for i in range(1, k + 1):
        pass
        # print("Frame", i, "now has", len(frames[i].cubes), "cubes.")


def rec_block_cube():
    log.block_cnt += 1
    start_time = time.perf_counter()
    global nkobl
    global unknown
    global show_block_info
    if show_block_info:
        print("rec_block_cube")
    states = []
    ct = 0
    cnt = 0
    while len(obligation_queue) != 0:
        if show_block_info:
            print("obligation_queue size:", len(obligation_queue))
        obligation_queue.sort()
        cnt += 1

        obl = obligation_queue[0]
        sat = frames[obl.frame_k].solver
        # sat.show_info()
        if is_inductive(sat, obl.state.latches, True)  == True:
            # print("successfully block cube")
            del obligation_queue[0]
            tmp_core = list(core)
            generalize(tmp_core, obl.frame_k, 1)

            # print("tmp_core: ",tmp_core)
            # generalize(tmp_core, obl.frame_k, 1)
            key = 0
            k = obl.frame_k + 1
            # print("tmp_core:",tmp_core)
            for k in range(obl.frame_k + 1, depth() + 1):
                key == 2
                if is_inductive(frames[k].solver, tmp_core, False) == False:
                    key = 1
                    break
            if key == 0:
                k += 1
            if k > depth() + 1:
                k = depth() + 1
            pushpo = False
            la = obl.state.latches
            for ci in frames[k].cubes:
                lemma = ci
                if len(la) < len(lemma):
                    break
                all_included = True
                for elem in lemma:
                    # 检查 la 中是否存在与 elem 绝对值相同的元素
                    if not any(abs(la_elem) == abs(elem) for la_elem in la):
                        all_included = False
                        break
                if all_included:
                    pushpo = True  # 对应 pushpo = 1
                    nkobl += 1
                    break  # 找到匹配后跳出循环
            add_cube(tmp_core, k, True, False, k - obl.frame_k + (1 if (len(tmp_core) < len(core)) else 0))
            if k <= depth():  
                # print("k:",k,"  depth:",depth())
                obligation_queue.append(Obligation(obl.state, k, obl.depth))
        else:
            if show_block_info:
                print("block cube failed")
            if cnt > 2147483640:
                unknown = True
                end_time = time.perf_counter()
                log.block_timer += (end_time - start_time)
                return False
            if obl.state.failed_depth and obl.state.failed_depth <= obl.depth + obl.frame_k:
                obligation_queue.sort()
                # 移除队列首个元素
                if obligation_queue:
                    obligation_queue.pop(0)  # 假设是列表，pop(0) 移除首个元素
                # 传递失败深度给下一个状态
                if obl.state.next is not None:
                    obl.state.next.failed_depth = obl.state.failed_depth
                continue  # 继续处理下一个义务

            # 第二个条件判断：检查失败次数和深度
            if obl.state.failed >= 5 and (obl.depth + obl.frame_k) > depth():
                obligation_queue.sort()
                # 移除队列首个元素
                if obligation_queue:
                    obligation_queue.pop(0)
                # 更新当前状态的失败深度
                obl.state.failed_depth = obl.depth + obl.frame_k
                # 传递失败深度给下一个状态
                if obl.state.next is not None:
                    obl.state.next.failed_depth = obl.state.failed_depth
                continue  # 继续处理下一个义务

            # 生成新状态并处理
            s = State()  # 创建新 State 实例
            states.append(s)  # 将新状态添加到全局状态列表
            if obl.frame_k == 0:
                # 处理 frame_k 为 0 的情况：提取输入和锁存器值
                s.clear()  # 清空状态的输入和锁存器
                # 提取输入值
                for i in range(num_inputs):
                    ipt = sat.val(inputs[i])
                    if ipt != 0:
                        s.inputs.append(ipt)
                # 提取锁存器值
                for i in range(num_latches):
                    l = sat.val(latches[i])
                    if l != 0:
                        s.latches.append(l)
                # 设置反例相关信息
                s.next = obl.state
                cex_state_idx = s
                find_cex = True
                # print("end rec_block_cube")
                end_time = time.perf_counter()
                log.block_timer += (end_time - start_time)
                return False   # 返回求解结果

            else:
                # 处理 frame_k 不为 0 的情况：从 SAT 求解器提取状态
                extract_state_from_sat(sat, s, obl.state, obl.frame_k)
                # 向义务队列插入新义务
                new_obligation = Obligation(s, obl.frame_k - 1, obl.depth + 1)
                obligation_queue.append(new_obligation)  # 假设用 append 插入队列
                obligation_queue.sort()
    # print("end rec_block_cube")
    end_time = time.perf_counter()
    log.block_timer += (end_time - start_time)
    return True



def propagate():
    log.propagate_cnt += 1
    start_time = time.perf_counter()
    global bad
    global show_propagate_info
    start_k = 1
    if top_frame_cannot_reach_bad == True:
        start_k = depth()
    if show_propagate_info:
        print("Propagate from frame", start_k)
    for i in range(start_k, depth() + 1):
        ckeep = 0
        cprop = 0
        idx = 0  
        cubes_list = list(frames[i].cubes)
        while idx < len(cubes_list):
            ci = cubes_list[idx] 
            # print("Checking cube at index", idx, ":", ci)
            if is_inductive(frames[i].solver, ci, True):
                # print("true")
                cprop += 1
                if len(core) < len(ci):
                    add_cube(core, i+1, True, True, 1)
                else:
                    add_cube(core, i+1, False, True, 0)
                cubes_list.pop(idx) 
                    
            else:
                ckeep += 1
                idx += 1  
        # frames[i].cubes = set(cubes_list)   
        frames[i].cubes.clear()
        frames[i].cubes.update(cubes_list)
        if len(frames[i].cubes) == 0:
            if len(frames[i].cubes) == 0:
                # 初始化变量
                invariant = None
                new_and_gate = None
                first_cube = True  # Python中用True/False表示布尔值
                badcube = []  # 假设Cube类已定义
                badcube.clear()    # 清空cube
                badcube.append(bad)
                badcube_tuple = tuple(badcube)
                frames[i+1].cubes.add(badcube_tuple)
                # frames[i+1].cubes.add(badcube)  # 假设用set存储cubes，使用add方法
                
                # 处理约束条件
                for l in constraints:
                    badcube.clear()
                    badcube.append(-l)
                    frames[i+1].cubes.add(tuple(badcube))
                
                
                # 处理证书输出
                if False:
                    # 合并后续帧的cubes
                    for d in range(i+2, depth() + 2):  # Python range是左闭右开，所以+2
                        for c in frames[d].cubes:
                            frames[i+1].cubes.add(c)
                    
                    # 处理每个cube构建AND门
                    for c in frames[i+1].cubes:
                        cc = list(c)  # 复制cube（frames 存的是 tuple）
                        if len(cc) == 0:
                            cc.append(-1)
                        
                        # 排序并反转，假设Lit_CMP()对应lambda表达式
                        cc.sort(key=lambda x: abs(x))  # 按绝对值排序
                        cc.reverse()  # 反转列表
                        
                        first_bit = True
                        for l in cc:
                            if first_bit:
                                new_and_gate = l
                                first_bit = False
                                continue
                            
                            # 计算新的AND门索引
                            o = 1 + num_inputs + num_latches + num_ands + 1
                            # 根据绝对值大小决定参数顺序
                            if abs(new_and_gate) > abs(l):
                                ands.append(And(o, new_and_gate, l))
                            else:
                                ands.append(And(o, l, new_and_gate))
                            
                            new_and_gate = o
                            num_ands += 1
                        
                        # 处理第一个cube和后续cube的逻辑
                        if first_cube:
                            invariant = -new_and_gate
                            first_cube = False
                            continue
                        
                        # 创建新的AND门
                        o = 1 + num_inputs + num_latches + num_ands + 1
                        if abs(new_and_gate) > abs(invariant):
                            ands.append(And(o, -new_and_gate, invariant))
                        else:
                            ands.append(And(o, invariant, -new_and_gate))
                        
                        invariant = o
                        num_ands += 1
                    
                    # 最终处理 
                    bad = -invariant
            end_time = time.perf_counter()
            log.propagate_timer += (end_time - start_time)
            return True
    end_time = time.perf_counter()
    log.propagate_timer += (end_time - start_time)
    return False

# def initialize(aig):  #把aig转化为cnf
#     return convert_ands_to_clauses(aig["ands"])

def aiger_to_dimacs(lit):
    res = lit >> 1
    if lit & 1 == 1:
        return -res-1
    else:
        return res+1

def new_frame():     #创建新的帧
    last = len(frames)
    frame =  Frame()
    frames.append(frame)
    global satelite1
    satelite1 = encode_translation(frames[last].solver,satelite1)
    assert satelite1 != None
    for l in constraints_prime:
        frames[last].solver.add(l)
        frames[last].solver.add(0)
    
def translate_to_dimacs():
    global blif
    global bad_prime 
    global bad
    global primed_first_dimacs
    variables.append(Variable(0, "NULL"))
    variables.append(Variable(1, "False"))

    # BLIF格式变量编号分配
    # 输入信号
    for i in range(num_inputs):
        variables.append(Variable(blif.inputs[i], None, 'i', i, 0))
        inputs.append(blif.inputs[i])

    # 锁存器（latch）
    for i in range(num_latches):
        variables.append(Variable(blif.latches[i][1], None, 'l', i, 0))
        latches.append(blif.latches[i][1])

    # AND门
    for i in range(num_ands):
        o = blif.ands[i][0]
        in1 = blif.ands[i][1]
        in2 = blif.ands[i][2]
        # 直接使用BLIF信号编号
        variables.append(Variable(o, None, 'a', i, 0))
        ands.append([blif.ands[i][0], in1, in2])

    # XOR门
    for i in range(num_xors):
        o = blif.xors[i][0]
        in1 = blif.xors[i][1]
        in2 = blif.xors[i][2]
        variables.append(Variable(o, None, 'x', i, 0))
        xors.append([blif.xors[i][0], in1, in2])

    # OR门
    for i in range(num_ors):
        o = blif.ors[i][0]
        in1 = blif.ors[i][1]
        in2 = blif.ors[i][2]
        variables.append(Variable(o, None, 'o', i, 0))
        ors.append([blif.ors[i][0], in1, in2])

    # 锁存器next/初始值
    for i in range(num_latches):
        l = 2 + num_inputs + i
        al = blif.latches[i]
        # al: (input编号, output编号, 初始值)
        nexts.append(al[0])
        if al[2] == 0:
            init_state.append(-al[1])
        elif al[2] == 1:
            init_state.append(al[1])

    # 约束（如有）
    for i in range(num_constraints):
        cst = blif.constraints[i]
        constraints.append(cst)

    primed_first_dimacs = len(variables)

    # 添加primed变量（输入、锁存器）
    for i in range(num_inputs):
        # print(f"输入信号: {blif.inputs[i]}")
        il= prime_lit(blif.inputs[i])
        # variables.append(Variable(len(variables), None, 'i', i, 1))
    for i in range(num_latches):
        # print(f"锁存器: {blif.latches[i][1]}")
        ll = prime_lit(blif.latches[i][1])
        # variables.append(Variable(len(variables), None, 'l', i, 1))

    # 约束prime
    for i in range(num_constraints):
        pl = prime_lit(constraints[i])
        constraints_prime.append(pl)

    # bad信号（假设blif.outputs[0]为bad）
    bad = blif.outputs[0] if blif.outputs else None
    bad_prime = prime_lit(bad) if bad is not None else None
    # for var in variables:
    #     print(var.name)

    
def pdr_main(blif_data):
    global num_inputs
    global num_latches
    global num_constraints
    global num_ands
    global num_xors
    global num_ors
    global earliest_strengthened_frame
    global top_frame_cannot_reach_bad
    global unknown
    global blif
    blif = blif_data
    # print(blif.inputs)
    # print(blif.outputs)
    # print(blif.latches)
    # print(blif.ands)
    # print(blif.xors)
    # print(blif.ors)
    num_inputs = len(blif.inputs)
    num_latches = len(blif.latches)
    num_ands = len(blif.ands)
    num_xors = len(blif.xors)
    num_ors = len(blif.ors)
    num_constraints = len(blif.constraints)
    translate_to_dimacs()
    satelite = None
    rs = SATSolver()
    satelite = encode_translation(rs, satelite)
    new_frame() #初始帧
    
    encode_init_condition(frames[0].solver)
    new_frame()
    # for c in frames[1].solver.clauses:
    #     print("c: ",c)
    new_frame()
    
    assert depth() == 1, f"深度应该为1"
    top_frame_cannot_reach_bad = True
    earliest_strengthened_frame = depth()
    result = 10
    ct = 0
    cnt = 0
    while True:
        cnt += 1
        if cnt > 2147483640:  #强制退出协议
            unknown = True
            break
        
        s = State()   #全状态
        flag = get_pre_of_bad(s)
        # print("latches:",s.latches)
        if flag == True:   #如果存在义务
            # print("flag")
            obligation_queue.clear() #清空义务列表
            # print("s的编号是： ",s.index)
            obligation_queue.append(Obligation(s, depth()-1, 1)) #加入新义务
            top_frame_cannot_reach_bad = False #现在会到达bad
            if rec_block_cube() == False:  #无法处理义务说明不安全
                result = 10
                break
            else:
                for p in states:
                    del p
        else:   #没有义务就看看能不能结束
            assert len(obligation_queue) == 0, f"存在未完成的义务"
            if propagate() == True:  #能结束就退出
                result =20
                break
            new_frame()  #不能结束就进下一层
            top_frame_cannot_reach_bad = True
            earliest_strengthened_frame = depth()
    if unknown == True:
        result = 0
    log.print_statistics()
    return result,log

