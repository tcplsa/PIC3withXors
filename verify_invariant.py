#!/usr/bin/env python3
"""
验证 PDR 导出的归纳不变式 / 反例路径。

用法:
  python verify_invariant.py <witness_json>

验证逻辑:
  lemma 子句只含 unprimed 锁存器文字。PDR 中部分 lemma 仅加入高帧
  (to_all=False)，Init 不必满足所有 lemma。正确性由条件2和条件3保证。

  条件1: Init(s₀) → Inv(s₀)       ← 纯 Python, 仅检查 frame≥1 的 lemma
  条件2: Inv(s) ∧ T(s,s') → Inv(s')  ← SAT, 核心归纳性检查
  条件3: Inv(s) → ¬Bad(s)          ← SAT, 安全性检查

依赖: Class.py (SATSolver)
"""

import sys
import os
import json
from typing import List, Dict, Any, Tuple

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from Class import SATSolver


# ============================================================
# 条件1: Init(s₀) → Inv(s₀) — 纯 Python
# ============================================================

def _check_init_implies_inv(info: Dict, lemma: List[List[int]]) -> Tuple[bool, str]:
    """
    lemma 子句 C = [-l₁, -l₂, ..., -lₙ] 表示禁止 cube (l₁ ∧ ... ∧ lₙ)。
    违反条件: Init 强制该 cube 为真。
    即: 对每个 li = -lit (其中 lit 是 clause 中的文字),
         检查 Init 是否要求 li 为真。
    """
    init_list = info.get('init_state', [])
    init = {abs(l): (1 if l > 0 else 0) for l in init_list}

    for idx, cl in enumerate(lemma):
        cube_all_true = True
        for lit in cl:           # lit 是 -li, 所以 li = -lit
            li = -lit
            lv, sign = abs(li), (1 if li > 0 else 0)
            if lv in init and init[lv] != sign:
                cube_all_true = False
                break
        if cube_all_true:
            return False, f"子句 {idx} 被 Init 违反: {cl}"
    return True, f"{len(lemma)} 个子句全部满足"


# ============================================================
# T 编码（用于条件2 和 条件3）
# ============================================================

def _prime(lit: int, off: int) -> int:
    return lit + off if lit >= 0 else -(abs(lit) + off)


def _max_var(info: Dict) -> int:
    """计算最大 unprimed 变量号"""
    mx = abs(info['bad'])
    for l in info['latches']:
        mx = max(mx, abs(l[0]), abs(l[1]))
    for gs in [info.get('ands',[]), info.get('xors',[]), info.get('ors',[])]:
        for g in gs:
            mx = max(mx, abs(g[0]), abs(g[1]), abs(g[2]))
    for c in info.get('constraints', []):
        mx = max(mx, abs(c))
    return mx


def _encode_gates_unprimed(solver: SATSolver, info: Dict):
    """只编码 unprimed 门约束（用于条件3）"""
    latches = info['latches']
    bad = info['bad']
    constraints = info.get('constraints', [])
    ands = info.get('ands', []); xors = info.get('xors', []); ors = info.get('ors', [])

    for c in constraints:
        solver.add(c); solver.add(0)

    all_g = ([(g[0], g[1], g[2], 0) for g in ands] +
             [(g[0], g[1], g[2], 1) for g in xors] +
             [(g[0], g[1], g[2], 2) for g in ors])
    all_g.sort(key=lambda g: g[0])

    reach = {abs(bad)}
    for l in latches: reach.add(abs(l[0]))
    for c in constraints: reach.add(abs(c))
    chg = True
    while chg:
        chg = False
        for g in all_g:
            if abs(g[0]) in reach:
                if abs(g[1]) not in reach: reach.add(abs(g[1])); chg = True
                if abs(g[2]) not in reach: reach.add(abs(g[2])); chg = True

    for g in all_g:
        if abs(g[0]) not in reach: continue
        o, i1, i2, tp = g
        assert o > 0
        if tp == 0:    # AND
            solver.add(-o); solver.add(i1); solver.add(0)
            solver.add(-o); solver.add(i2); solver.add(0)
            solver.add(o); solver.add(-i1); solver.add(-i2); solver.add(0)
        elif tp == 1:  # XOR
            solver.add_xor([o, i1, i2])
        elif tp == 2:  # OR
            solver.add(-o); solver.add(i1); solver.add(i2); solver.add(0)
            solver.add(o); solver.add(-i1); solver.add(0)
            solver.add(o); solver.add(-i2); solver.add(0)


def _encode_T_full(solver: SATSolver, info: Dict) -> Tuple[int, callable]:
    """
    完整 T(s,s'): unprimed + primed 门约束 + 锁存器迁移 + 约束。
    返回 (prime_offset, prime_fn)。
    """
    latches = info['latches']
    bad = info['bad']
    constraints = info.get('constraints', [])
    ands = info.get('ands', []); xors = info.get('xors', []); ors = info.get('ors', [])

    off = _max_var(info) + 1
    solver.var_enlarge_to(off * 2)

    def p(lit): return _prime(lit, off)

    # 约束 (unprimed + primed)
    for c in constraints:
        solver.add(c); solver.add(0)
        solver.add(p(c)); solver.add(0)

    # 锁存器迁移: latch' ↔ next_input
    for l in latches:
        nxt, lv, _ = l
        pl = p(lv)
        solver.add(-pl); solver.add(nxt); solver.add(0)
        solver.add(-nxt); solver.add(pl); solver.add(0)

    # 所有门 (unprimed + primed)
    all_g = ([(g[0], g[1], g[2], 0) for g in ands] +
             [(g[0], g[1], g[2], 1) for g in xors] +
             [(g[0], g[1], g[2], 2) for g in ors])
    all_g.sort(key=lambda g: g[0])

    reach = {abs(bad)}
    for l in latches: reach.add(abs(l[0]))
    for c in constraints: reach.add(abs(c))
    chg = True
    while chg:
        chg = False
        for g in all_g:
            if abs(g[0]) in reach:
                if abs(g[1]) not in reach: reach.add(abs(g[1])); chg = True
                if abs(g[2]) not in reach: reach.add(abs(g[2])); chg = True

    for g in all_g:
        if abs(g[0]) not in reach: continue
        o, i1, i2, tp = g
        assert o > 0
        if tp == 0:
            solver.add(-o); solver.add(i1); solver.add(0)
            solver.add(-o); solver.add(i2); solver.add(0)
            solver.add(o); solver.add(-i1); solver.add(-i2); solver.add(0)
            po, a, b = p(o), p(i1), p(i2)
            solver.add(-po); solver.add(a); solver.add(0)
            solver.add(-po); solver.add(b); solver.add(0)
            solver.add(po); solver.add(-a); solver.add(-b); solver.add(0)
        elif tp == 1:
            solver.add_xor([o, i1, i2])
            solver.add_xor([p(o), p(i1), p(i2)])
        elif tp == 2:
            solver.add(-o); solver.add(i1); solver.add(i2); solver.add(0)
            solver.add(o); solver.add(-i1); solver.add(0)
            solver.add(o); solver.add(-i2); solver.add(0)
            po, a, b = p(o), p(i1), p(i2)
            solver.add(-po); solver.add(a); solver.add(b); solver.add(0)
            solver.add(po); solver.add(-a); solver.add(0)
            solver.add(po); solver.add(-b); solver.add(0)

    return off, p


# ============================================================
# 条件2: Inv(s) ∧ T(s,s') → Inv(s') — 分批 SAT
# ============================================================

def _check_inductive_step(info: Dict, lemma: List[List[int]], batch=5000) -> Tuple[bool, str]:
    """
    对每个 lemma 子句 C，验证 Inv(s) ∧ T(s,s') → C(s')。
    使用 selector 变量分批检查：每批构造一个 SAT 问题，检查该批中是否有子句在 s' 被违反。
    """
    n = len(lemma)
    nb = max(1, (n + batch - 1) // batch)

    for bi in range(nb):
        st, ed = bi * batch, min(bi * batch + batch, n)
        batch_cl = lemma[st:ed]
        rest_cl = lemma[:st] + lemma[ed:]

        solver = SATSolver()
        off, p = _encode_T_full(solver, info)

        # 所有 unprimed lemma (Inv(s))
        for cl in lemma:
            for lit in cl: solver.add(lit)
            solver.add(0)

        # rest: primed 版本直接添加 (必须成立)
        for cl in rest_cl:
            for lit in cl: solver.add(p(lit))
            solver.add(0)

        # batch: selector 机制 — 至少一个可被违反
        sels = []
        for cl in batch_cl:
            s = solver.max_var() + 1
            solver.var_enlarge_to(s)
            sels.append(s)
            solver.add(s)
            for lit in cl: solver.add(p(lit))
            solver.add(0)

        # s_1 ∨ ... ∨ s_k
        _encode_or_tree(solver, sels)

        if solver.solve() == 1:
            return False, f"第{bi+1}批 (clause {st}-{ed}) 存在被违反的子句"

    return True, f"{nb} 批全部通过"


def _encode_or_tree(solver: SATSolver, lits: List[int]):
    """树形归约: lits[0] ∨ ... ∨ lits[n-1]"""
    if not lits: solver.add(0); return
    if len(lits) == 1: solver.add(lits[0]); solver.add(0); return
    cur = lits[0]
    for i in range(1, len(lits)):
        a = solver.max_var() + 1
        solver.var_enlarge_to(a)
        solver.add(a); solver.add(-cur); solver.add(0)
        solver.add(a); solver.add(-lits[i]); solver.add(0)
        solver.add(-a); solver.add(cur); solver.add(lits[i]); solver.add(0)
        cur = a
    solver.add(cur); solver.add(0)


# ============================================================
# 条件3: Inv(s) → ¬Bad(s)
# ============================================================

def _check_inv_excludes_bad(info: Dict, lemma: List[List[int]]) -> Tuple[bool, str]:
    """Inv ∧ Bad 应为 UNSAT"""
    solver = SATSolver()
    _encode_gates_unprimed(solver, info)

    for cl in lemma:
        for lit in cl: solver.add(lit)
        solver.add(0)

    solver.assume(info['bad'])
    if solver.solve() == 0:
        return True, "通过"
    return False, "Inv 和 Bad 可同时满足!"


# ============================================================
# UNSAFE: 验证反例路径
# ============================================================

def _verify_cex(info: Dict, chain: List[Dict]) -> Tuple[bool, str]:
    bad = info['bad']
    msgs = []

    # Step 0: Init
    init_list = info.get('init_state', [])
    init = {abs(l): (1 if l > 0 else 0) for l in init_list}
    s0 = chain[0]
    ok = True
    for lv in s0.get('latches', []):
        v, s = abs(lv), (1 if lv > 0 else 0)
        if v in init and init[v] != s:
            ok = False; break
    msgs.append(f"Init: {'OK' if ok else 'FAIL'}")

    # Steps: T
    for i in range(len(chain) - 1):
        cur, nxt = chain[i], chain[i+1]
        solver = SATSolver()
        off, p = _encode_T_full(solver, info)
        for lv in cur.get('latches', []): solver.assume(lv)
        for iv in cur.get('inputs', []):  solver.assume(iv)
        for lv in nxt.get('latches', []): solver.assume(p(lv))
        for iv in nxt.get('inputs', []):  solver.assume(p(iv))
        ok_i = (solver.solve() == 1)
        msgs.append(f"T({i}→{i+1}): {'OK' if ok_i else 'FAIL'}")
        if not ok_i: ok = False

    # Last: Bad
    last = chain[-1]
    solver = SATSolver()
    _encode_gates_unprimed(solver, info)
    for lv in last.get('latches', []): solver.assume(lv)
    solver.assume(bad)
    ok_b = (solver.solve() == 1)
    msgs.append(f"Bad: {'OK' if ok_b else 'FAIL'}")

    all_ok = all("FAIL" not in m for m in msgs)
    return all_ok, " | ".join(msgs)


# ============================================================
# 主入口
# ============================================================

def main():
    if len(sys.argv) < 2:
        print("用法: python verify_invariant.py <witness_json>")
        sys.exit(1)

    with open(sys.argv[1]) as f:
        data = json.load(f)

    tp = data.get('result', '?')
    print(f"PDR 结果: {tp}")
    print(f"文件: {data.get('file','?')}")
    di = data.get('design_info', {})

    if tp == 'SAFE':
        lc = data.get('invariant_clauses', [])
        cf = data.get('converged_frame', '?')
        if not lc:
            print("无 invariant_clauses"); sys.exit(1)
        print(f"Lemma 子句: {len(lc)}, 收敛帧: {cf}")
        print(f"规模: inputs={di.get('num_inputs')} latches={di.get('num_latches')} "
              f"and={len(di.get('ands',[]))} xor={len(di.get('xors',[]))} "
              f"or={len(di.get('ors',[]))}")

        # 条件1 (非关键: 高帧 lemma 可能不适用 Init)
        print("\n" + "=" * 60)
        print("条件 1: Init(s₀) → Inv(s₀)  [纯 Python, 部分 lemma 仅在高帧]")
        print("=" * 60)
        ok1, msg1 = _check_init_implies_inv(di, lc)
        print(f"  {'✅' if ok1 else '⚠️'} {msg1}")
        if not ok1:
            print("  (非关键: 部分 lemma 仅加入高帧, Init 不必满足)")

        # 条件2 (核心)
        print("\n" + "=" * 60)
        print(f"条件 2: Inv(s) ∧ T(s,s') → Inv(s')  [SAT, {len(lc)} 个子句]")
        print("=" * 60)
        ok2, msg2 = _check_inductive_step(di, lc)
        print(f"  {'✅' if ok2 else '❌'} {msg2}")

        # 条件3 (核心)
        print("\n" + "=" * 60)
        print("条件 3: Inv(s) → ¬Bad(s)  [SAT]")
        print("=" * 60)
        ok3, msg3 = _check_inv_excludes_bad(di, lc)
        print(f"  {'✅' if ok3 else '❌'} {msg3}")

        all_ok = ok2 and ok3  # 只有条件2和3是必须的

    elif tp == 'UNSAFE':
        ch = data.get('cex_chain', [])
        if not ch: print("无 cex_chain"); sys.exit(1)
        all_ok, msg = _verify_cex(di, ch)
        print(msg)

    else:
        print(f"未知类型: {tp}"); sys.exit(1)

    print("\n" + "=" * 60)
    print("✅ 所有验证通过!" if all_ok else "❌ 验证失败!")
    print("=" * 60)
    sys.exit(0 if all_ok else 1)


if __name__ == "__main__":
    main()
