from collections import OrderedDict

def parse_blif_core(path):
    """核心BLIF解析：提取结构、识别取反对和缓冲器"""
    inputs = []
    outputs = []
    names_blocks = []
    latches = []
    used_signals = set()
    neg_pairs = {}
    eq_pairs = {}

    try:
        with open(path, 'r', encoding='utf-8') as f:
            raw_lines = [l.rstrip('\n').rstrip('\r') for l in f]
    except FileNotFoundError:
        raise FileNotFoundError(f"BLIF文件不存在：{path}")
    except Exception as e:
        raise RuntimeError(f"读取BLIF失败：{e}")

    # 预处理：合并续行（以 \ 结尾的行与下一行拼接）
    lines = []
    i = 0
    while i < len(raw_lines):
        line = raw_lines[i]
        i += 1
        # 当行以 \ 结尾时，与后续行拼接（去掉 \）
        while line.rstrip().endswith('\\') and i < len(raw_lines):
            line = line.rstrip()[:-1] + ' ' + raw_lines[i].strip()
            i += 1
        lines.append(line.rstrip('\n'))

    i = 0
    line_count = len(lines)
    while i < line_count:
        line = lines[i].strip()
        i += 1

        if not line or line.startswith('#'):
            continue

        if line.startswith('.inputs'):
            input_signals = line.split()[1:]
            input_signals = [s for s in input_signals if s not in ['rst_n', 'clk', '\\']]
            inputs.extend(input_signals)
            used_signals.update(input_signals)
            continue

        if line.startswith('.outputs'):
            output_signals = line.split()[1:]
            output_signals = [s for s in output_signals if s != '\\']
            outputs.extend(output_signals)
            used_signals.update(output_signals)
            continue

        if line.startswith('.names'):
            parts = line.split()
            # 过滤掉续行符 \
            parts = [p for p in parts if p != '\\']
            nm_inputs = parts[1:-1] if len(parts) > 1 else []
            nm_output = parts[-1] if len(parts) >= 1 else ''
            rows = []
            while i < line_count:
                next_line = lines[i].strip()
                i += 1
                if not next_line or next_line.startswith('#'):
                    continue
                if next_line.startswith('.'):
                    i -= 1
                    break
                toks = next_line.split()
                if len(toks) < 1:
                    continue
                if len(toks) >=2:
                    rows.append((toks[0], toks[1]))
                elif len(toks) == 1:
                    rows.append((toks[0]))
                else:
                    rows.append(0)
            if  len(rows) == 0:
                rows.append('0')
                # rows.append((toks[0], toks[1] if len(toks) >= 2 else '0'))
            # if not rows and len(nm_inputs) == 1 and nm_output == '0':
            #     rows.append(('0', '0'))
            if not rows and len(nm_output) > 0:
                continue
            if len(nm_inputs) == 1 and len(rows) == 1:
                src_sig = nm_inputs[0]
                if rows[0] == ('0', '1'):
                    neg_pairs[nm_output] = src_sig
                    used_signals.add(src_sig)
                elif rows[0] == ('1', '1'):
                    eq_pairs[nm_output] = src_sig
                    used_signals.add(src_sig)
                continue
            used_signals.update(nm_inputs)
            used_signals.add(nm_output)
            names_blocks.append((nm_inputs, nm_output, rows))
            continue

        if line.startswith('.latch'):
            parts = line.split()
            if len(parts) >= 3:
                input_sig = parts[1]
                output_sig = parts[2]
                init_val = 1 if (len(parts) >= 5 and parts[4] == '1') else 0
                used_signals.add(input_sig)
                used_signals.add(output_sig)
                latches.append({'type':'latch', 'input':input_sig, 'output':output_sig, 'init':init_val})
            continue

        if line.startswith('.gate'):
            # .gate XOR A=sig1 B=sig2 O=sig3  → 转成.names块的真值表
            parts = line.split()
            if len(parts) < 2:
                continue
            gate_type = parts[1].upper()
            params = {}
            for p in parts[2:]:
                if '=' in p:
                    k, v = p.split('=', 1)
                    params[k] = v
            if gate_type == 'XOR' and 'A' in params and 'B' in params and 'O' in params:
                nm_in = [params['A'], params['B']]
                nm_out = params['O']
                # XOR真值表：01→1, 10→1
                rows = [('01', '1'), ('10', '1')]
                used_signals.update(nm_in)
                used_signals.add(nm_out)
                names_blocks.append((nm_in, nm_out, rows))
            elif gate_type == 'AND' and 'A' in params and 'B' in params and 'O' in params:
                nm_in = [params['A'], params['B']]
                nm_out = params['O']
                rows = [('11', '1')]
                used_signals.update(nm_in)
                used_signals.add(nm_out)
                names_blocks.append((nm_in, nm_out, rows))
            elif gate_type == 'OR' and 'A' in params and 'B' in params and 'O' in params:
                nm_in = [params['A'], params['B']]
                nm_out = params['O']
                rows = [('01', '1'), ('10', '1'), ('11', '1')]
                used_signals.update(nm_in)
                used_signals.add(nm_out)
                names_blocks.append((nm_in, nm_out, rows))
            elif gate_type == 'NOT' and 'A' in params and 'O' in params:
                neg_pairs[params['O']] = params['A']
                used_signals.add(params['A'])
            elif gate_type == 'BUFF' and 'A' in params and 'O' in params:
                eq_pairs[params['O']] = params['A']
                used_signals.add(params['A'])
            continue

        if line.startswith('.subckt'):
            parts = line.split()
            if len(parts) < 2 or parts[1] not in ['$dff', '$_SDFF_PN0_', '$_SDFF_PP0_', '$_DFF_P_', '$_SDFFE_PP0N_']:
                continue
            params = {}
            for param in parts[2:]:
                if '=' in param:
                    k, v = param.split('=', 1)
                    params[k] = v
            if 'D' not in params or 'Q' not in params:
                continue
            d_sig, q_sig = params['D'], params['Q']
            clk_sig = params.get('C', 'clk')
            rst_sig = params.get('R', None)
            used_signals.add(d_sig)
            used_signals.add(q_sig)
            used_signals.add(clk_sig)
            if rst_sig:
                used_signals.add(rst_sig)
            latches.append({
                'type':'dff', 'input':d_sig, 'output':q_sig, 
                'clk':clk_sig, 'rst':rst_sig, 'init':0
            })
            continue

        if line.startswith('.gate'):
            parts = line.split()
            if len(parts) < 2 or parts[1] != 'XOR':
                continue
            params = {}
            for param in parts[2:]:
                if '=' in param:
                    k, v = param.split('=', 1)
                    params[k] = v
            if 'A' not in params or 'B' not in params or 'O' not in params:
                continue
            a_sig, b_sig, o_sig = params['A'], params['B'], params['O']
            used_signals.update([a_sig, b_sig, o_sig])
            # 转换为等价的 .names 块（XOR 真值表：01 1 / 10 1）
            names_blocks.append(([a_sig, b_sig], o_sig, [('01', '1'), ('10', '1')]))
            continue

        if line.startswith('.end'):
            break

    return inputs, outputs, names_blocks, latches, used_signals, neg_pairs, eq_pairs
