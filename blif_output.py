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

# 真值表 → 门类型查找表 (v00,v01,v10,v11) 共16种组合
# 格式: key=(v00,v01,v10,v11), value=(gate_type, invert_output, (invert_a, invert_b)|None)
_GATE_LUT = {
    # 全0 / 全1 → 常量
    ('0','0','0','0'): ('constraint', False, None),
    ('1','1','1','1'): ('constraint', True, None),
    # AND 系: 仅一个位置为1
    ('1','0','0','0'): ('and', False, (True, True)),    # ~a AND ~b  (仅 00=1)
    ('0','1','0','0'): ('and', False, (True, False)),   # ~a AND b   (仅 01=1)
    ('0','0','1','0'): ('and', False, (False, True)),   # a AND ~b   (仅 10=1)
    ('0','0','0','1'): ('and', False, (False, False)),  # a AND b    (仅 11=1)
    # AND 系取反: 仅一个位置为0
    ('0','1','1','1'): ('and', True, (True, True)),     # ~(~a AND ~b)
    ('1','0','1','1'): ('and', True, (True, False)),    # ~(~a AND b)
    ('1','1','0','1'): ('and', True, (False, True)),    # ~(a AND ~b)
    ('1','1','1','0'): ('and', True, (False, False)),   # NAND
    # XOR / XNOR
    ('0','1','1','0'): ('xor', False, (False, False)),  # a XOR b
    ('1','0','0','1'): ('xor', True, (False, False)),   # XNOR
    # OR / NOR
    ('1','0','0','0'): ('or', True, (False, False)),    # NOR (= ~a AND ~b, 等价)
    ('0','1','1','1'): ('or', False, (False, False)),   # a OR b
}


def _identify_gate_type(nm_inputs, rows):
    """识别2输入门类型：AND/XOR/OR及其反相、输入取反 (优化版: LUT + 直接字符比较)"""
    # 0输入 → 常量约束
    if len(nm_inputs) == 0:
        if len(rows) == 1:
            value = rows[0] if isinstance(rows[0], str) else str(rows[0])
            return 'constraint', value == '1', None
        return 'constraint', False, None

    # 单输入
    if len(nm_inputs) == 1:
        if len(rows) == 1:
            row = rows[0]
            if isinstance(row, str):
                return 'constraint', row == '1', None
            return 'unknown', False, None
        return 'unknown', False, None

    # === 2输入门: 直接填充真值表，O(1) 查找 ===
    has_zero = False
    for e in rows:
        if isinstance(e, (list, tuple)) and len(e) >= 2 and e[1] == '0':
            has_zero = True
            break
    default = '1' if has_zero else '0'

    # tt = [v00, v01, v10, v11]
    tt = [default, default, default, default]

    for entry in rows:
        if isinstance(entry, str):
            pat, val = entry, '1'
        elif len(entry) == 2:
            pat, val = entry[0], entry[1]
        else:
            continue

        if len(pat) != 2 or val not in ('0', '1'):
            continue

        # 直接字符匹配 — 避免 all(zip()) 和函数调用开销
        p0, p1 = pat[0], pat[1]
        if p0 not in '01-' or p1 not in '01-':
            continue

        if p0 == '-':
            if p1 == '-':  # -- 匹配全部
                tt = [val, val, val, val]
                break
            elif p1 == '0':  # -0 → idx 0,2
                tt[0] = tt[2] = val
            else:            # -1 → idx 1,3
                tt[1] = tt[3] = val
        elif p1 == '-':
            if p0 == '0':    # 0- → idx 0,1
                tt[0] = tt[1] = val
            else:            # 1- → idx 2,3
                tt[2] = tt[3] = val
        else:
            # 精确匹配: 00, 01, 10, 11
            idx = (0 if p0 == '0' else 2) + (0 if p1 == '0' else 1)
            tt[idx] = val

    return _GATE_LUT.get((tt[0], tt[1], tt[2], tt[3]), ('unknown', False, None))

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
        sig2rep: dict{信号名: 代表元}
        sig2sign: dict{信号名: 符号(1/-1)}
    """
    parent = {}
    sig2sign = {}

    def find(x):
        if x not in parent:
            parent[x] = x
            sig2sign[x] = 1
        if parent[x] != x:
            orig = parent[x]
            root = find(orig)
            parent[x] = root
            sig2sign[x] *= sig2sign[orig]
        return parent[x]

    def union(x, y, sign):
        px, py = find(x), find(y)
        if px != py:
            parent[py] = px
            sig2sign[py] = -sig2sign[x] if sign else sig2sign[x]

    for a, b in neg_pairs.items():
        union(a, b, 1)

    for a, b in eq_pairs.items():
        union(a, b, 0)

    # 收集所有涉及信号 (用 set.update 避免列表拼接拷贝)
    all_signals = set(neg_pairs)
    all_signals.update(neg_pairs.values())
    all_signals.update(eq_pairs)
    all_signals.update(eq_pairs.values())

    # 按代表元分组
    root2sigs = {}
    for x in all_signals:
        px = find(x)
        if px not in root2sigs:
            root2sigs[px] = OrderedDict()
        root2sigs[px][x] = sig2sign[x]

    # 构建 SigPair 和 sig2rep (一次遍历等价类)
    SigPair = OrderedDict()
    sig2rep = {}
    for root, class_sigs in root2sigs.items():
        # class_sigs: {sig: sign_relative_to_root}
        for sig, self_sign in class_sigs.items():
            sig2rep[sig] = root
            other_map = OrderedDict()
            for other_sig, other_sign in class_sigs.items():
                if other_sig != sig:
                    # other 相对 sig 的符号 = other_sign * self_sign (都是±1, 乘除等价)
                    other_map[other_sig] = other_sign * self_sign
            SigPair[sig] = other_map

    return SigPair, sig2rep, sig2sign

def kahn_layering(inputs, outputs, ands, xors, ors, sig2rep):
    """
    Kahn算法分层，inputs为起点，返回每个信号的层级dict (优化版)。
    """
    graph = {}
    indegree = {}
    _get = sig2rep.get  # local ref 加速

    # 合并所有门一次遍历
    for gate_info in ands:
        o, i1, i2 = gate_info[0], gate_info[1], gate_info[2]
        of = _get(o, o); i1f = _get(i1, i1); i2f = _get(i2, i2)
        graph.setdefault(i1f, []).append(of)
        graph.setdefault(i2f, []).append(of)
        indegree[of] = indegree.get(of, 0) + 2
        indegree.setdefault(i1f, 0); indegree.setdefault(i2f, 0)

    for gate_info in xors:
        o, i1, i2 = gate_info[0], gate_info[1], gate_info[2]
        of = _get(o, o); i1f = _get(i1, i1); i2f = _get(i2, i2)
        graph.setdefault(i1f, []).append(of)
        graph.setdefault(i2f, []).append(of)
        indegree[of] = indegree.get(of, 0) + 2
        indegree.setdefault(i1f, 0); indegree.setdefault(i2f, 0)

    for gate_info in ors:
        o, i1, i2 = gate_info[0], gate_info[1], gate_info[2]
        of = _get(o, o); i1f = _get(i1, i1); i2f = _get(i2, i2)
        graph.setdefault(i1f, []).append(of)
        graph.setdefault(i2f, []).append(of)
        indegree[of] = indegree.get(of, 0) + 2
        indegree.setdefault(i1f, 0); indegree.setdefault(i2f, 0)

    for inp in inputs:
        indegree.setdefault(_get(inp, inp), 0)
    for out in outputs:
        indegree.setdefault(_get(out, out), 0)

    # Kahn拓扑排序分层
    layer = {}
    queue = deque()
    for node, deg in indegree.items():
        if deg == 0:
            queue.append(node)
            layer[node] = 0
    while queue:
        u = queue.popleft()
        ul = layer[u] + 1
        for v in graph.get(u, ()):
            d = indegree[v] - 1
            indegree[v] = d
            if d == 0:
                queue.append(v)
                layer[v] = ul
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
    # 预先构建 SigPair 反向索引，避免 update_var_number 中 O(n²) 遍历
    rev_index = {}
    for sig, others in SigPair.items():
        for other in others:
            if other not in rev_index:
                rev_index[other] = []
            rev_index[other].append(sig)

    for sig in signals_to_fix:
        resolved = _resolve_equivalence(sig, eq_pairs)
        if resolved in name2var and name2var[resolved] < 0:
            update_var_number(resolved, abs(name2var[resolved]), name2var, SigPair, sig2rep, sig2sign, rev_index)

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





def update_var_number(target_sig, new_var, name2var, SigPair, sig2rep, sig2sign, _rev_index=None):
    """
    直接修改name2var中target_sig的编号，并同步所有等价/相反信号的编号。
    _rev_index: 预先构建的反向索引 {信号: [包含该信号的其他信号列表]}，避免O(n²)
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
        sign = sig2sign[rep] // sig2sign[target_sig]
        name2var[rep] = new_var * sign

    # 反向索引：使用预构建的索引避免 O(n²) 遍历
    if _rev_index is not None and target_sig in _rev_index:
        for sig in _rev_index[target_sig]:
            if sig in SigPair and target_sig in SigPair[sig]:
                sign = SigPair[sig][target_sig]
                name2var[sig] = new_var * sign
    else:
        # 无索引时回退到 O(n) 遍历（兼容旧调用）
        for sig, others in SigPair.items():
            if sig == target_sig:
                continue
            if target_sig in others:
                sign = others[target_sig]
                name2var[sig] = new_var * sign

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
        