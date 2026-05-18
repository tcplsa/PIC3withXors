from collections import OrderedDict, defaultdict, deque
from blif_input import parse_blif_core

class BLIFParserResult:
    """BLIF解析结果封装类"""
    def __init__(self):
        self.inputs = []                # 顶层输入信号编号列表
        self.outputs = []               # 顶层输出信号编号列表
        self.names_blocks = []          # 原始有效.names块列表
        self.ands = []                  # AND门（变量编号）
        self.xors = []                  # XOR门（变量编号）
        self.ors = []                   # OR门（变量编号）
        self.latches = []               # 锁存器信息（input编号, output编号, 初始值）→ output必为正
        self.name2var = OrderedDict()   # 信号名→变量编号映射
        self.var_count = 0              # 有效变量总数
        self.neg_pairs = {}             # 取反对映射：取反信号→(源变量编号, 符号)
        self.eq_pairs = {}              # 缓冲器等价映射：输出→输入
        self.constraints = []

def _identify_gate_type(nm_inputs, rows):
    """识别2输入门类型：AND/XOR/OR及其反相、输入取反

    返回: (gate_type, invert_output, invert_inputs)
      - gate_type: 'and' | 'xor' | 'or' | 'constraint' | 'unknown'
      - invert_output: bool，输出是否取反
      - invert_inputs: (invert_a, invert_b) | None，各输入是否取反

    支持BLIF中只列出输出为1的行的精简写法，例如:
      - 11 1  → 标准AND (a AND b)
      - 10 1  → a AND ~b (第二个输入取反)
      - 01 1  → ~a AND b (第一个输入取反)
      - 00 1  → ~a AND ~b (两个输入都取反)
      - 11 0  → NAND (输出取反)
    """
    # 0输入 → 常量约束
    if len(nm_inputs) == 0:
        if len(rows) == 1:
            value = rows[0] if isinstance(rows[0], str) else str(rows[0])
            return 'constraint', value == '1', None
        return 'constraint', False, None

    # 单输入 → 在 blif_input.py 中已转化为 neg_pairs/eq_pairs，不应到达此处
    # 但为安全保留处理
    if len(nm_inputs) == 1:
        if len(rows) == 1:
            row = rows[0]
            if isinstance(row, str):
                return 'constraint', row == '1', None
            return 'unknown', False, None
        return 'unknown', False, None

    # === 2输入门 ===
    # 约定：列出value=1的行 → 未列出默认0；列出value=0的行 → 未列出默认1
    # 即有显式0值行 → 默认值翻转为1
    has_zero_value = any(
        (isinstance(e, (list, tuple)) and len(e) >= 2 and e[1] == '0')
        for e in rows
    )
    default_val = '1' if has_zero_value else '0'
    full_table = {'00': default_val, '01': default_val, '10': default_val, '11': default_val}

    def row_matches(pattern, key):
        return all(pc == '-' or pc == kc for pc, kc in zip(pattern, key))

    for entry in rows:
        if isinstance(entry, str):
            pattern = entry
            value = '1'
        elif len(entry) == 2:
            pattern, value = entry[0], entry[1]
        else:
            continue

        if len(pattern) != 2 or value not in ('0', '1'):
            continue
        if all(c in '01-' for c in pattern):
            for key in full_table:
                if row_matches(pattern, key):
                    full_table[key] = value

    v00, v01, v10, v11 = full_table['00'], full_table['01'], full_table['10'], full_table['11']

    # 先检查常量约束（全0或全1）
    if v00 == '0' and v01 == '0' and v10 == '0' and v11 == '0':
        return 'constraint', False, None           # 输出恒为0
    if v00 == '1' and v01 == '1' and v10 == '1' and v11 == '1':
        return 'constraint', True, None            # 输出恒为1

    # ---- AND 及其所有变种 ----
    # 核心思路：数"1"的个数来判断门类型
    # 标准AND: 仅 11→1，其余→0
    if v11 == '1' and v00 == '0' and v01 == '0' and v10 == '0':
        return 'and', False, (False, False)       # a AND b
    if v11 == '0' and v00 == '1' and v01 == '1' and v10 == '1':
        return 'and', True, (False, False)         # NAND

    # a AND ~b: 仅 10→1，其余→0
    if v10 == '1' and v00 == '0' and v01 == '0' and v11 == '0':
        return 'and', False, (False, True)         # a AND ~b
    if v10 == '0' and v00 == '1' and v01 == '1' and v11 == '1':
        return 'and', True, (False, True)          # ~(a AND ~b)

    # ~a AND b: 仅 01→1，其余→0
    if v01 == '1' and v00 == '0' and v10 == '0' and v11 == '0':
        return 'and', False, (True, False)         # ~a AND b
    if v01 == '0' and v00 == '1' and v10 == '1' and v11 == '1':
        return 'and', True, (True, False)          # ~(~a AND b)

    # ~a AND ~b: 仅 00→1，其余→0
    if v00 == '1' and v01 == '0' and v10 == '0' and v11 == '0':
        return 'and', False, (True, True)          # ~a AND ~b
    if v00 == '0' and v01 == '1' and v10 == '1' and v11 == '1':
        return 'and', True, (True, True)           # ~(~a AND ~b)

    # ---- XOR ----
    if v00 == '0' and v01 == '1' and v10 == '1' and v11 == '0':
        return 'xor', False, (False, False)        # a XOR b
    if v00 == '1' and v01 == '0' and v10 == '0' and v11 == '1':
        return 'xor', True, (False, False)         # XNOR

    # ---- OR ----
    if v00 == '0' and v01 == '1' and v10 == '1' and v11 == '1':
        return 'or', False, (False, False)         # a OR b
    if v00 == '1' and v01 == '0' and v10 == '0' and v11 == '0':
        return 'or', True, (False, False)          # NOR

    return 'unknown', False, None

def _split_names_to_ands_xors(names_blocks):
    """将.names块拆解为AND/XOR/OR门和约束

    返回: ands, xors, ors, constraints
      - ands/xors/ors: [(output, in1, in2, invert_output, (invert_in1, invert_in2))]
      - constraints: [(output, value)]  value=1常真, 0常假
    """
    ands, xors, ors = [], [], []
    constraints = []
    for nm_inputs, nm_output, rows in names_blocks:
        gate_type, invert_output, invert_inputs = _identify_gate_type(nm_inputs, rows)

        if gate_type == 'constraint':
            constraints.append((nm_output, 1 if invert_output else 0))
            continue

        # 只处理正好2个输入的门
        if len(nm_inputs) != 2:
            if gate_type == 'unknown' and len(nm_inputs) >= 3:
                pass  # 多输入门，合理跳过
            else:
                print(f"Warning: 无法处理的{len(nm_inputs)}输入门 {nm_output} = f({', '.join(nm_inputs)}), gate_type={gate_type}")
            continue

        if gate_type == 'and':
            ands.append((nm_output, nm_inputs[0], nm_inputs[1], invert_output, invert_inputs))
        elif gate_type == 'xor':
            xors.append((nm_output, nm_inputs[0], nm_inputs[1], invert_output, invert_inputs))
        elif gate_type == 'or':
            ors.append((nm_output, nm_inputs[0], nm_inputs[1], invert_output, invert_inputs))
        elif gate_type == 'unknown':
            print(f"Warning: 未知门类型 {nm_output} = f({', '.join(nm_inputs)}), rows={rows}")
    return ands, xors, ors, constraints

def _resolve_equivalence(sig_name, eq_pairs):
    """递归解析缓冲器等价映射"""
    while sig_name in eq_pairs:
        sig_name = eq_pairs[sig_name]
    return sig_name

# def build_not_equiv_classes(neg_pairs):
#     """
#     构建非门等价类，每对(a, b)满足a = ~b或b = ~a，归为同一等价类。
#     返回: {代表元: [所有等价信号名]}, 以及信号->代表元的映射。
#     """
#     parent = {}
#     def find(x):
#         while parent.get(x, x) != x:
#             parent[x] = parent.get(parent[x], parent[x])
#             x = parent[x]
#         return x
#     def union(x, y):
#         px, py = find(x), find(y)
#         if px != py:
#             parent[py] = px
#     for a, b in neg_pairs.items():
#         # a = ~b 或 b = ~a
#         union(a, b)
#     # 收集等价类
#     SigPair = OrderedDict()
#     for x in set(list(neg_pairs.keys()) + list(neg_pairs.values())):
#         px = find(x)
#         SigPair[px].append(x)
#     # 信号到代表元
#     sig2rep = {x: find(x) for x in set(list(neg_pairs.keys()) + list(neg_pairs.values()))}
#     return SigPair, sig2rep

def build_not_equiv_classes(neg_pairs, eq_pairs):
    """
    构建非门等价类，每对(a, b)满足a = ~b或b = ~a，归为同一等价类。
    返回: 
        SigPair: OrderedDict{信号名: {可替换信号名: 符号(1/-1)}} （1=等价，-1=相反）
        sig2rep: dict{信号名: 代表元} （信号→代表元映射）
        sig2sign: dict{信号名: 符号(1/-1)} （信号相对代表元的符号）
    """
    parent = {}          # 并查集父节点映射：key=信号，value=父节点
    sig2sign = {}        # 信号相对父节点的符号：key=信号，value=1/-1（初始为1）

    def find(x):
        """查找代表元，同时更新符号（路径压缩时传递符号）"""
        if x not in parent:
            parent[x] = x
            sig2sign[x] = 1  # 初始：自身是代表元，符号为1
        
        # 路径压缩 + 符号传递
        if parent[x] != x:
            orig_parent = parent[x]
            root = find(parent[x])  # 递归找根节点
            # 更新父节点（路径压缩）
            parent[x] = root
            # 更新符号：x相对根节点的符号 = x相对原父节点的符号 * 原父节点相对根节点的符号
            sig2sign[x] *= sig2sign[orig_parent]
        return parent[x]

    def union(x, y, sign):
        """合并x和y（x = ~y），维护符号关系"""
        px = find(x)  # x的代表元
        py = find(y)  # y的代表元
        if px != py:
            # 合并：将py的父节点设为px，同时记录y相对px的符号（y = ~x → y的符号 = -1 * x的符号）
            parent[py] = px
            if sign == 1:
                # x的符号是sig2sign[x]（相对px），y = ~x → y相对px的符号 = -sig2sign[x]
                sig2sign[py] = -sig2sign[x]
            else:
                # x的符号是sig2sign[x]，y = x → y相对px的符号 = sig2sign[x]
                sig2sign[py] = sig2sign[x]

    # 初始化并合并所有非门对
    for a, b in neg_pairs.items():
        # a = ~b → 合并a和b，维护符号关系
        union(a, b, 1)

    for a, b in eq_pairs.items():
        # a = b → 合并a和b，维护符号关系
        union(a, b, 0)
    
    # 第一步：先按代表元收集等价类（所有信号+符号）
    root2sigs = OrderedDict()  # 代表元: {信号: 符号}
    all_signals = set(list(neg_pairs.keys()) + list(neg_pairs.values()) + list(eq_pairs.keys()) + list(eq_pairs.values()))
    for x in all_signals:
        px = find(x)  # 确保路径压缩和符号更新完成
        if px not in root2sigs:
            root2sigs[px] = OrderedDict()
        root2sigs[px][x] = sig2sign[x]

    # 第二步：构建SigPair（每个信号都作为键，对应其等价类的所有可替换信号+符号）
    SigPair = OrderedDict()
    for sig in all_signals:
        # 找到当前信号的代表元，获取整个等价类的信号+符号
        root = find(sig)
        class_sigs = root2sigs[root]
        
        # 计算当前信号相对等价类中每个信号的符号
        sig2other = OrderedDict()
        sig_self_sign = sig2sign[sig]  # 当前信号相对代表元的符号
        for other_sig, other_sign in class_sigs.items():
            if other_sig != sig:
                # 符号规则：other_sig 相对 sig 的符号 = other_sign / sig_self_sign（即 other_sig = sign * sig）
                sign = other_sign / sig_self_sign  # 1/-1（因为都是±1，等价于相乘）
                sig2other[other_sig] = int(sign)  # 转为整数
        
        SigPair[sig] = sig2other

    # 信号到代表元的映射
    sig2rep = {x: find(x) for x in all_signals}

    return SigPair, sig2rep, sig2sign

def kahn_layering(inputs, outputs, ands, xors, ors, sig2rep):
    """
    Kahn算法分层，inputs为起点，返回每个信号的层级dict。
    ands/xors/ors 格式: [(output, in1, in2, invert_output, (invert_in1, invert_in2))]
    """
    graph = defaultdict(list)
    indegree = defaultdict(int)

    for gate_info in ands + xors + ors:
        o, i1, i2 = gate_info[0], gate_info[1], gate_info[2]
        of = sig2rep.get(o, o)
        i1f = sig2rep.get(i1, i1)
        i2f = sig2rep.get(i2, i2)
        graph[i1f].append(of)
        graph[i2f].append(of)
        indegree[of] += 2
        indegree.setdefault(i1f, 0)
        indegree.setdefault(i2f, 0)

    for inp in inputs:
        indegree.setdefault(sig2rep.get(inp, inp), 0)
    for out in outputs:
        indegree.setdefault(sig2rep.get(out, out), 0)

    # Kahn拓扑排序分层
    layer = {}
    queue = deque()
    for node in indegree:
        if indegree[node] == 0:
            queue.append(node)
            layer[node] = 0
    while queue:
        u = queue.popleft()
        for v in graph[u]:
            indegree[v] -= 1
            if indegree[v] == 0:
                queue.append(v)
                layer[v] = layer[u] + 1
    return layer

def assign_vars_by_layer(layer_dict, sig2rep):
    """
    按层级分配变量编号，层级小的编号小，同层内部可按名字排序。
    返回: {信号名: 变量编号}
    """
    sorted_items = sorted(layer_dict.items(), key=lambda x: (x[1], str(x[0])))
    name2var = OrderedDict()
    for idx, (name, l) in enumerate(sorted_items, 1):
        if l < 1e10:
            name2var[name] = idx
        else:
            rep = sig2rep.get(name, name)
            # 尝试从代表元获取编号
            if rep in name2var:
                name2var[name] = name2var[rep] * -1
            elif rep == name:
                # 自己在等价类中是代表元，但自身未分配编号
                # 给它分配一个新编号
                max_var = max(name2var.values()) if name2var else 0
                name2var[name] = max_var + 1
            else:
                # 代表元也未分配编号，为两者都分配
                max_var = max(name2var.values()) if name2var else 0
                name2var[rep] = max_var + 1
                name2var[name] = -name2var[rep]
    return name2var

def parse_blif_with_layered_vars(blif_path):
    """
    使用分层分配变量编号的BLIF解析主函数
    """
    inputs, outputs, names_blocks, latches, used_signals, neg_pairs, eq_pairs = parse_blif_core(blif_path)
    # 提取门电路
    ands_list, xors_list, ors_list, constraints = _split_names_to_ands_xors(names_blocks)
    # for ands in ands_list:
    #     print("AND gate:", ands)
    # for xors in xors_list:
    #     print("XOR gate:", xors)
    # for l in latches:
    #     print(f"锁存器: input={l['input']} output={l['output']} init={l['init']}")
    # 构建非门等价类
    not_pairs = {}
    for k, v in neg_pairs.items():
        not_pairs[k] = v
        not_pairs[v] = k
    equal_pairs = {}
    for k, v in eq_pairs.items():
        equal_pairs[k] = v
        equal_pairs[v] = k
    # print("neg_pairs:", not_pairs)
    # print("eq_pairs:", equal_pairs)
    SigPair, sig2rep, sig2sign = build_not_equiv_classes(not_pairs, equal_pairs)
    # print("SigPair 输出：")
    # for sig, replace_map in SigPair.items():
    #     print(f"{sig}: {dict(replace_map)}")
    
    # 获取所有涉及的信号（包括输入、输出、中间信号）
    # 先解析掉 eq_pair，避免等价信号重复进入 layer
    all_signals = set()
    for s in inputs:
        all_signals.add(_resolve_equivalence(s, eq_pairs))
    for s in outputs:
        all_signals.add(_resolve_equivalence(s, eq_pairs))
    for gate_info in ands_list + xors_list + ors_list:
        o, i1, i2 = gate_info[0], gate_info[1], gate_info[2]
        all_signals.update([
            _resolve_equivalence(o, eq_pairs),
            _resolve_equivalence(i1, eq_pairs),
            _resolve_equivalence(i2, eq_pairs),
        ])
    for latch in latches:
        all_signals.update([latch['input'], latch['output']])
    # neg_pairs/eq_pairs 的源信号也需要变量编号（如 extractxor 的常数"0"）
    for src in neg_pairs.values():
        all_signals.add(src)
    for src in eq_pairs.values():
        all_signals.add(src)
    # print("所有变量：",all_signals)
    # Kahn分层
    layer = kahn_layering(inputs, outputs, ands_list, xors_list, ors_list, sig2rep)
    # 确保所有信号都有层级信息（处理未出现在门中的信号）
    for signal in all_signals:
        if signal not in layer:
            layer[signal] = 1e10  # 默认为第0层（输入层或孤立信号）
        # layer["$aiger1$0b"] = 0
    # 按层级分配变量编号
    name2var = assign_vars_by_layer(layer, sig2rep)
    
    # 映射所有信号到变量编号

    def map_signal_to_var(sig_name, force_positive=False, force_update_var=None):
        """
        信号名转变量编号（处理取反）。
        force_update_var: 若指定，则将该信号及其等价/相反信号的编号全部同步为此值（正整数），并返回对应编号（考虑取反）。
        """
        original_sig = sig_name
        # 解析等价映射
        resolved_sig = _resolve_equivalence(sig_name, eq_pairs)
        # print(f"映射信号: 原始={original_sig} 解析后={resolved_sig}" )
        # force_positive为True时，自动同步所有等价/相反信号编号为正数
        if force_positive:
            # 以当前编号的绝对值为正编号进行同步
            if resolved_sig in name2var:
                update_var_number(resolved_sig, abs(name2var[resolved_sig]), name2var, SigPair, sig2rep, sig2sign)
            else:
                raise KeyError(f"信号{resolved_sig}未分配编号")
        if force_update_var is not None:
            # 直接同步所有等价/相反信号的编号
            update_var_number(resolved_sig, force_update_var, name2var, SigPair, sig2rep, sig2sign)
        if resolved_sig in name2var:
            var = name2var[resolved_sig]
        else:
            return None
            raise KeyError(f"信号{resolved_sig}未分配编号")
        return var

    def update_var_number(target_sig, new_var, name2var, SigPair, sig2rep, sig2sign):
        """
        直接修改name2var中target_sig的编号，并同步所有等价/相反信号的编号。
        target_sig: 目标信号名（不带~）
        new_var: 新的编号（正整数）
        name2var: {信号名: 变量编号}
        SigPair: {信号名: {等价/相反信号: 符号}}
        sig2rep: {信号名: 代表元}
        sig2sign: {信号名: 符号(1/-1)}
        """
        # 先更新自身
        name2var[target_sig] = new_var
        # 找到target_sig的等价类（所有等价/相反信号）
        if target_sig not in SigPair:
            return

        # 更新等价/相反信号
        for other_sig, sign in SigPair[target_sig].items():
            name2var[other_sig] = new_var * sign
        # 还要保证代表元的编号也同步
        rep = sig2rep[target_sig]
        if rep != target_sig:
            # 代表元编号 = new_var * (sig2sign[rep] / sig2sign[target_sig])
            sign = sig2sign[rep] // sig2sign[target_sig]
            name2var[rep] = new_var * sign
        # 反向：如果有信号的等价类包含target_sig，也要同步（防止SigPair只单向）
        for sig, others in SigPair.items():
            if sig == target_sig:
                continue
            if target_sig in others:
                sign = others[target_sig]
                name2var[sig] = new_var * sign
    
    # 映射输入、输出、锁存器
    # print("latches:",latches)

    # latches_var = []
    # for latch in latches:
    #     out_var = map_signal_to_var(latch['output'], force_positive=True)
    # # 映射门电路
    # ands_var = []
    # for out_sig, in1_sig, in2_sig, invert_out in ands_list:
    #     out_var = map_signal_to_var(out_sig, force_positive=True)

    # xors_var = []
    # for out_sig, in1_sig, in2_sig, invert_out in xors_list:
    #     out_var = map_signal_to_var(out_sig, force_positive=True)
    
    # ors_var = []
    # for out_sig, in1_sig, in2_sig, invert_out in ors_list:
    #     out_var = map_signal_to_var(out_sig, force_positive=True)
    # === 第一阶段：预处理所有需要为正的输出信号，统一翻转 ===
    # 收集所有需要 force_positive 的信号（门输出、latch输出）
    signals_to_fix = set()
    for gate_info in ands_list + xors_list + ors_list:
        signals_to_fix.add(gate_info[0])  # gate_info[0] = output
    for latch in latches:
        signals_to_fix.add(latch['output'])
    for inp in inputs:
        signals_to_fix.add(inp)
    # 在映射任何门之前，先将它们统一设置为正
    for sig in signals_to_fix:
        resolved = _resolve_equivalence(sig, eq_pairs)
        if resolved in name2var and name2var[resolved] < 0:
            update_var_number(resolved, abs(name2var[resolved]), name2var, SigPair, sig2rep, sig2sign)

    # 第二轮：直接根据 neg_pairs 修正逆变器信号的符号
    # SigPair 在多跳合并时符号会出错，所以用原始 neg_pairs 直接修正
    for neg_sig, src_sig in neg_pairs.items():
        if neg_sig in name2var and src_sig in name2var:
            v_neg = name2var[neg_sig]
            v_src = name2var[src_sig]
            # 两者同号 → 逆变器信号符号错误，翻转
            if (v_neg > 0) == (v_src > 0):
                name2var[neg_sig] = -v_neg

    # === 第二阶段：正式映射所有门（展平——输出无invert标志） ===
    # 规则：
    #   invert_out AND → 转OR，两个输入取反 (德摩根: ~(a&b) = ~a|~b)
    #   invert_out OR  → 转AND，两个输入取反 (德摩根: ~(a|b) = ~a&~b)
    #   invert_out XOR → 保持XOR，输出翻符号
    #   invert_inputs  → 直接翻转变量的符号
    latches_var = []
    for latch in latches:
        in_var = map_signal_to_var(latch['input'])
        out_var = map_signal_to_var(latch['output'])
        assert out_var is not None and out_var > 0, f"锁存器output {latch['output']} 编号为负或None"
        latches_var.append((in_var, out_var, latch['init']))
    latches_var.sort(key=lambda x: x[1])

    ands_var = []
    xors_var = []
    ors_var = []

    # 处理AND列表
    for gate_info in ands_list:
        out_sig, in1_sig, in2_sig, invert_out, invert_inputs = gate_info
        out_var = map_signal_to_var(out_sig)
        in1_var = map_signal_to_var(in1_sig)
        in2_var = map_signal_to_var(in2_sig)
        # 输入取反：翻转变量的符号
        if invert_inputs and invert_inputs[0]:
            in1_var = -in1_var
        if invert_inputs and invert_inputs[1]:
            in2_var = -in2_var
        out_var_abs = abs(out_var)
        if invert_out:
            # ~(a&b) = ~a|~b  → 转OR，输入取反
            ors_var.append((out_var_abs, -in1_var, -in2_var))
        else:
            ands_var.append((out_var_abs, in1_var, in2_var))

    # 处理XOR列表
    for gate_info in xors_list:
        out_sig, in1_sig, in2_sig, invert_out, invert_inputs = gate_info
        out_var = map_signal_to_var(out_sig)
        in1_var = map_signal_to_var(in1_sig)
        in2_var = map_signal_to_var(in2_sig)
        if invert_inputs and invert_inputs[0]:
            in1_var = -in1_var
        if invert_inputs and invert_inputs[1]:
            in2_var = -in2_var
        out_var_abs = abs(out_var)
        if invert_out:
            # ~(a^b) = ~a^b → 输入1取反，输出正
            xors_var.append((out_var_abs, -in1_var, in2_var))
        else:
            xors_var.append((out_var_abs, in1_var, in2_var))

    # 处理OR列表
    for gate_info in ors_list:
        out_sig, in1_sig, in2_sig, invert_out, invert_inputs = gate_info
        out_var = map_signal_to_var(out_sig)
        in1_var = map_signal_to_var(in1_sig)
        in2_var = map_signal_to_var(in2_sig)
        if invert_inputs and invert_inputs[0]:
            in1_var = -in1_var
        if invert_inputs and invert_inputs[1]:
            in2_var = -in2_var
        out_var_abs = abs(out_var)
        if invert_out:
            # ~(a|b) = ~a&~b  → 转AND，输入取反
            ands_var.append((out_var_abs, -in1_var, -in2_var))
        else:
            ors_var.append((out_var_abs, in1_var, in2_var))

    constraints_var = []
    for constr_sig, val in constraints:
        sig_var = map_signal_to_var(constr_sig)
        if sig_var is None:
            continue
        if val == 0:  # 常量为0 → 取反
            sig_var = -sig_var
        constraints_var.append(sig_var)
    # NOTE: 常数信号由电路结构自然保证，不额外加入约束
    # (原来 name2var["0"] 的约束在取反编码下会变成矛盾约束)

    ands_var.sort(key=lambda x: x[0])
    xors_var.sort(key=lambda x: x[0])
    ors_var.sort(key=lambda x: x[0])
    inputs_var = [map_signal_to_var(s) for s in inputs]
    outputs_var = [map_signal_to_var(s) for s in outputs]
    # 构建结果对象
    result = BLIFParserResult()
    result.inputs = [(v // abs(v) if v != 0 else 1) * (abs(v) + 1) for v in inputs_var]
    result.outputs = [(v // abs(v) if v != 0 else 1) * (abs(v) + 1) for v in outputs_var]
    result.constraints = [(v // abs(v) if v != 0 else 1) * (abs(v) + 1) for v in constraints_var]
    result.names_blocks = names_blocks  # 保持原始.names块不变
    result.ands = [((o // abs(o) if o != 0 else 1) * (abs(o) + 1), i1 // abs(i1) * (abs(i1) + 1), i2 // abs(i2) * (abs(i2) + 1)) for (o, i1, i2) in ands_var]
    result.xors = [((o // abs(o) if o != 0 else 1) * (abs(o) + 1), i1 // abs(i1) * (abs(i1) + 1), i2 // abs(i2) * (abs(i2) + 1)) for (o, i1, i2) in xors_var]
    result.ors = [((o // abs(o) if o != 0 else 1) * (abs(o) + 1), i1 // abs(i1) * (abs(i1) + 1), i2 // abs(i2) * (abs(i2) + 1)) for (o, i1, i2) in ors_var]
    result.latches = []
    for latch in latches_var:
        in_var, out_var, init = latch
        assert out_var > 0, f"锁存器output编号必须为正，当前为{out_var}"
        result.latches.append(((in_var // abs(in_var) if in_var != 0 else 1) * (abs(in_var) + 1), (out_var // abs(out_var) if out_var != 0 else 1) * (abs(out_var) + 1), init))
    result.name2var = name2var
    result.var_count = len(name2var)
    result.neg_pairs = neg_pairs
    result.eq_pairs = eq_pairs
    
    return result



if __name__ == '__main__':
    import sys
    blif_path = '/home/lyj238/wdl/IC3/pipeLinedAdder_final.blif'
    blif_path = '/home/lyj238/wdl/data/hwmcc15-benchmarks-single-blif/6s7.blif'
    try:
        print("=== 按层次分配变量编号的解析结果 ===")
        parser_result = parse_blif_with_layered_vars(blif_path)
        print(f"输入信号编号: {parser_result.inputs}")
        print(f"输出信号编号: {parser_result.outputs}")
        print(f"约束条件（信号编号，值）: {parser_result.constraints}")
        print(f"总变量数: {parser_result.var_count}")
        print(f"AND门数: {len(parser_result.ands)} | XOR门数: {len(parser_result.xors)} | OR门数: {len(parser_result.ors)} | 锁存器数: {len(parser_result.latches)}")
        print(f"AND门信息（o, i1, i2）: {parser_result.ands}")
        print(f"XOR门信息（o, i1, i2）: {parser_result.xors}")
        print(f"OR门信息（o, i1, i2）: {parser_result.ors}")
        print(f"锁存器信息（input, output, init）: {parser_result.latches}")
        for latch in parser_result.latches:
            assert latch[1] > 0, f"锁存器output {latch[1]} 非正！"
        print("✅ 所有锁存器output编号均为正")
        # print(f"变量映射（信号名 -> 编号）: {list(parser_result.name2var.items())}")
        
        # print("\n=== 连续变量编号解析结果（对比）===")
        # parser_result2 = parse_blif_with_continuous_vars(blif_path)
        # print(f"总变量数: {parser_result2.var_count}")
        # print(f"变量映射前10项: {list(parser_result2.name2var.items())[:10]}")
        
    except Exception as e:
        print(f"解析失败: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
        