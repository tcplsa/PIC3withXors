#!/usr/bin/env python3
"""
AAG to BLIF converter with complete XOR/XNOR extraction.
Reads an ASCII AIG file, recognizes all XOR/XNOR gate patterns,
and writes a flat BLIF netlist using .names for generic logic
and .gate XOR for extracted XORs (with explicit inverters for XNOR).
No .subckt is generated.

AAG header format: aag M I L O A
  M = max variable index
  I = number of inputs
  L = number of latches
  O = number of outputs
  A = number of AND gates

Token order per AIGER spec: inputs -> latches -> outputs -> AND gates.
Input lines store even literals (var * 2).
Latch lines store cur_lit nxt_lit pairs.
Output lines store literals (may be odd for inverted outputs).
"""

import sys
import os
from pathlib import Path

def read_aag(filename):
    with open(filename) as f:
        lines = f.readlines()
    lines = [l.strip() for l in lines if l.strip() and not l.startswith('#')]

    header = lines[0].split()
    if len(header) < 6:
        raise ValueError("Invalid AAG header (need at least 6 fields)")
    M, I, L, O, A = map(int, header[1:6])
    # 扩展字段: B=bad输出数, C=约束输出数, J=justice, F=fairness
    extended_fields = list(map(int, header[6:10]))
    B, C, J, F = (extended_fields + [0]*4)[:4]

    tokens = []
    for line in lines[1:]:
        tokens.extend(line.split())

    idx = 0

    # Inputs: store variable indices (lit // 2)
    inputs = [int(tokens[idx + i]) // 2 for i in range(I)]
    idx += I

    # Latches (before outputs per AIGER spec): L pairs (cur_lit, nxt_lit)
    latches = []
    for _ in range(L):
        if idx + 1 >= len(tokens):
            break
        cur_lit = int(tokens[idx])
        nxt_lit = int(tokens[idx + 1])
        latches.append((cur_lit, nxt_lit))
        idx += 2

    # Outputs: raw literals (after latches per AIGER spec)
    outputs = [int(tokens[idx + i]) for i in range(O)]
    idx += O

    # Bad outputs (B literals, after regular outputs)
    bad_outputs = [int(tokens[idx + i]) for i in range(B)]
    idx += B

    # Constraint outputs (C literals, after bad outputs)
    constraint_outputs = [int(tokens[idx + i]) for i in range(C)]
    idx += C

    # AND gates: A triples of (lhs_lit, rhs0_lit, rhs1_lit)
    and_gates = []
    for _ in range(A):
        if idx + 2 >= len(tokens):
            raise ValueError(f"Expected {A} AND gates, only found {len(and_gates)}")
        out_var = int(tokens[idx]) // 2
        lhs = int(tokens[idx + 1])
        rhs = int(tokens[idx + 2])
        and_gates.append((out_var, lhs, rhs))
        idx += 3

    return M, inputs, outputs, latches, and_gates, bad_outputs, constraint_outputs


def lit_to_signal(lit):
    """Returns (node_id, invert) from a literal."""
    if lit == 0:
        return 0, 0
    if lit == 1:
        return 0, 1
    return lit // 2, lit & 1


class Node:
    __slots__ = ('id', 'fanin0', 'inv0', 'fanin1', 'inv1',
                 'is_xor', 'xor_a', 'xor_b', 'xor_b_inv',
                 'is_xor_sub', 'refcount')
    def __init__(self, nid):
        self.id = nid
        self.fanin0 = self.fanin1 = 0
        self.inv0 = self.inv1 = 0
        self.is_xor = False
        self.xor_a = self.xor_b = 0
        self.xor_b_inv = False
        self.is_xor_sub = False
        self.refcount = 0


def build_netlist(M, inputs, outputs, latches, and_gates,
                  bad_outputs=None, constraint_outputs=None):
    nodes = [Node(i) for i in range(M + 1)]
    and_node_ids = set()

    for out_id, lhs_lit, rhs_lit in and_gates:
        and_node_ids.add(out_id)
        n = nodes[out_id]
        fa0, iv0 = lit_to_signal(lhs_lit)
        fa1, iv1 = lit_to_signal(rhs_lit)
        n.fanin0 = fa0
        n.inv0 = iv0
        n.fanin1 = fa1
        n.inv1 = iv1

    # Count refs from AND gates
    for nid in and_node_ids:
        n = nodes[nid]
        nodes[n.fanin0].refcount += 1
        nodes[n.fanin1].refcount += 1
    # Count refs from outputs
    for lit in outputs:
        nid, _ = lit_to_signal(lit)
        nodes[nid].refcount += 1
    # Count refs from bad outputs
    if bad_outputs:
        for lit in bad_outputs:
            nid, _ = lit_to_signal(lit)
            nodes[nid].refcount += 1
    # Count refs from constraint outputs
    if constraint_outputs:
        for lit in constraint_outputs:
            nid, _ = lit_to_signal(lit)
            nodes[nid].refcount += 1
    # Count refs from latch next-state signals
    for cur_lit, nxt_lit in latches:
        nid, _ = lit_to_signal(nxt_lit)
        nodes[nid].refcount += 1

    return nodes, and_node_ids


def extract_xors(nodes, and_node_ids):
    """
    Detect XOR and XNOR patterns from the AIG and mark them.

    A XOR(a,b) in AIG:
      g0 = AND(¬a, ¬b)   -> inputs both inverted  [1,1]
      g1 = AND(a, b)      -> inputs neither inverted [0,0]
      g2 = AND(¬g0, ¬g1)  -> both inputs inverted
      -> pattern (1,1,0,0) or symmetric (0,0,1,1)

    A XNOR(a,b) in AIG:
      g0 = AND(a, ¬b)     -> one inverted [0,1]
      g1 = AND(¬a, b)     -> the opposite [1,0]
      g2 = AND(¬g0, ¬g1)  -> both inputs inverted
      -> pattern (0,1,1,0) or symmetric (1,0,0,1)

    For XNOR we emit XOR(a, ¬b) by adding an inverter on one input.
    """
    for n in nodes:
        if n.id == 0 or n.id not in and_node_ids:
            continue

        # g2 must have both inputs inverted
        if not (n.inv0 and n.inv1):
            continue

        d1 = nodes[n.fanin0]
        d2 = nodes[n.fanin1]
        if d1.id not in and_node_ids or d2.id not in and_node_ids:
            continue

        # --- XOR: (1,1,0,0) or (0,0,1,1) ---
        if (d1.inv0 == d1.inv1 and d2.inv0 == d2.inv1
                and d1.inv0 != d2.inv0):
            # 必须验证两个AND共用同一对输入（只是极性相反）
            if not ((d1.fanin0 == d2.fanin0 and d1.fanin1 == d2.fanin1) or
                    (d1.fanin0 == d2.fanin1 and d1.fanin1 == d2.fanin0)):
                continue
            src = d1 if d1.inv0 == 0 else d2
            a_var, b_var = src.fanin0, src.fanin1
            if a_var != 0 and b_var != 0:
                n.is_xor = True
                n.xor_a = a_var
                n.xor_b = b_var
                n.xor_b_inv = False
                if d1.refcount == 1:
                    d1.is_xor_sub = True
                if d2.refcount == 1:
                    d2.is_xor_sub = True
                continue

        # --- XNOR: (0,1,1,0) or (1,0,0,1) ---
        if (d1.inv0 != d1.inv1 and d2.inv0 != d2.inv1
                and d1.inv0 == d2.inv1 and d1.inv1 == d2.inv0):
            # 必须验证两个AND共用同一对输入（只是极性互补）
            if not ((d1.fanin0 == d2.fanin0 and d1.fanin1 == d2.fanin1) or
                    (d1.fanin0 == d2.fanin1 and d1.fanin1 == d2.fanin0)):
                continue
            # d1 = AND(a, ¬b): a is non-inverted input, ¬b is inverted input
            if d1.inv0 == 0:
                a_var = d1.fanin0
                b_var = d1.fanin1
            else:
                a_var = d1.fanin1
                b_var = d1.fanin0
            # XOR(a, ¬b) = XNOR(a, b)
            if a_var != 0 and b_var != 0:
                n.is_xor = True
                n.xor_a = a_var
                n.xor_b = b_var
                n.xor_b_inv = True
                if d1.refcount == 1:
                    d1.is_xor_sub = True
                if d2.refcount == 1:
                    d2.is_xor_sub = True
                continue


def write_blif(nodes, inputs, outputs, latches, M, and_node_ids, out_filename,
               bad_outputs=None, constraint_outputs=None):
    with open(out_filename, 'w') as f:
        f.write(".model top\n")

        in_names = [f"in{i}" for i in range(len(inputs))]
        f.write(".inputs " + " ".join(in_names) + "\n")

        # 所有输出 = 常规输出 + bad输出（constraint不放入.outputs，用.names约束表示）
        all_output_names = [f"out{i}" for i in range(len(outputs))]
        if bad_outputs:
            all_output_names += [f"bad{i}" for i in range(len(bad_outputs))]
        f.write(".outputs " + " ".join(all_output_names) + "\n")

        # Name mapping
        id_to_name = {}
        for i, nid in enumerate(inputs):
            id_to_name[nid] = f"in{i}"
        for cur_lit, _ in latches:
            cv = cur_lit // 2
            id_to_name[cv] = f"latch{cv}"
        id_to_name[0] = "_const0"

        inv_count = 0

        # 显式定义常量信号，避免 NOT(0) 被误识别为 constraint
        f.write(".names _const0\n0\n")
        f.write(".names _const1\n1\n")

        def get_name(nid):
            if nid in id_to_name:
                return id_to_name[nid]
            name = f"n{nid}"
            id_to_name[nid] = name
            return name

        for nid in and_node_ids:
            get_name(nid)

        # Output buffers (常规输出)
        for i, lit in enumerate(outputs):
            drv, inv = lit_to_signal(lit)
            drv_name = "_const1" if (drv == 0 and inv) else ("_const0" if drv == 0 else get_name(drv))
            out_name = f"out{i}"
            if inv and drv != 0:
                f.write(f".names {drv_name} {out_name}\n0 1\n")
            else:
                f.write(f".names {drv_name} {out_name}\n1 1\n")

        # Bad output buffers
        if bad_outputs:
            for i, lit in enumerate(bad_outputs):
                drv, inv = lit_to_signal(lit)
                drv_name = "_const1" if (drv == 0 and inv) else ("_const0" if drv == 0 else get_name(drv))
                out_name = f"bad{i}"
                if inv and drv != 0:
                    f.write(f".names {drv_name} {out_name}\n0 1\n")
                else:
                    f.write(f".names {drv_name} {out_name}\n1 1\n")

        # Constraint outputs: 写入 0 输入 .names 块（BLIF 解析器会识别为约束）
        if constraint_outputs:
            for i, lit in enumerate(constraint_outputs):
                drv, inv = lit_to_signal(lit)
                if drv == 0:
                    # 常量约束: _const1 必须为真(恒成立)，_const0 必须为真(矛盾)
                    # 为安全起见跳过常量1约束，常量0约束显式写出
                    if inv:
                        # _const1 必须为1 → 恒成立，跳过
                        continue
                    else:
                        # _const0 必须为1 → 矛盾约束
                        f.write(f".names _const0\n1\n")
                else:
                    drv_name = get_name(drv)
                    if inv:
                        # 约束: ~drv 必须为真 → drv 必须为 0
                        f.write(f".names {drv_name}\n0\n")
                    else:
                        # 约束: drv 必须为真
                        f.write(f".names {drv_name}\n1\n")

        # Internal logic
        for nid in sorted(and_node_ids):
            n = nodes[nid]
            if n.is_xor_sub:
                continue

            out_name = get_name(n.id)

            if n.is_xor:
                a_name = get_name(n.xor_a)
                b_name = get_name(n.xor_b)
                if n.xor_b_inv:
                    inv_name = f"_i{inv_count}"
                    inv_count += 1
                    f.write(f".names {b_name} {inv_name}\n0 1\n")
                    b_name = inv_name
                f.write(f".gate XOR A={a_name} B={b_name} O={out_name}\n")
            else:
                a_name = get_name(n.fanin0)
                b_name = get_name(n.fanin1)

                a_true = 1 if not n.inv0 else 0
                b_true = 1 if not n.inv1 else 0
                pattern = f"{a_true}{b_true}"
                f.write(f".names {a_name} {b_name} {out_name}\n{pattern} 1\n")

        # Latches
        for cur_lit, nxt_lit in latches:
            cur_id = cur_lit // 2
            if cur_id == 0:
                continue
            cur_name = get_name(cur_id)
            nxt_id, nxt_inv = lit_to_signal(nxt_lit)
            if nxt_id == 0:
                # 常量信号：0→_const0，1→_const1，无需额外 NOT 门
                nxt_name = "_const1" if nxt_inv else "_const0"
                f.write(f".latch {nxt_name} {cur_name} 0\n")
            else:
                nxt_name = get_name(nxt_id)
                if nxt_inv:
                    inv_name = f"_i{inv_count}"
                    inv_count += 1
                    f.write(f".names {nxt_name} {inv_name}\n0 1\n")
                    f.write(f".latch {inv_name} {cur_name} 0\n")
                else:
                    f.write(f".latch {nxt_name} {cur_name} 0\n")

        f.write(".end\n")


def main():
    aag_dir = "/home/lyj238/wdl/data/hardproblems_aag"
    blif_dir = "/home/lyj238/wdl/data/hardproblems-blif-xor"
    os.makedirs(blif_dir, exist_ok=True)

    aag_files = sorted(Path(aag_dir).glob("*.aag"))
    print(f"Found {len(aag_files)} AAG files")

    for i, aag_file in enumerate(aag_files, 1):
        blif_file = os.path.join(blif_dir, aag_file.stem + ".blif")
        print(f"[{i}/{len(aag_files)}] {aag_file.name} -> {blif_file}")
        M, inputs, outputs, latches, and_gates, bad_outputs, constraint_outputs = read_aag(str(aag_file))
        nodes, and_node_ids = build_netlist(M, inputs, outputs, latches, and_gates,
                                            bad_outputs, constraint_outputs)
        extract_xors(nodes, and_node_ids)
        write_blif(nodes, inputs, outputs, latches, M, and_node_ids, str(blif_file),
                   bad_outputs, constraint_outputs)
        if bad_outputs:
            print(f"  Bad outputs: {len(bad_outputs)}")
        if constraint_outputs:
            print(f"  Constraints: {len(constraint_outputs)}")

    print(f"Done. Output: {blif_dir}")


if __name__ == "__main__":
    main()
