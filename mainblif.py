import sys
import os
import shutil
# from Aiger import *
from PDRblif import *
from blif_output import parse_blif_with_layered_vars
import time


show_aig = 0

def get_file_extension(file_path):
    """获取文件的文件名和扩展名"""
    filename, ext = os.path.splitext(file_path)
    return filename, ext

def file_hash(path):
    """计算文件的SHA256哈希值（用于判断文件是否重复）"""
    import hashlib
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(8192), b''):
            h.update(chunk)
    return h.hexdigest()

def copy_to_unsolved(filepath):
    """
    将文件复制到 Unsolved_files 文件夹（避免重复）
    :param filepath: 原始文件路径
    :return: 复制后的文件路径（None表示复制失败）
    """
    try:
        repo_root = os.path.dirname(os.path.abspath(__file__))
        unsolved_dir = os.path.join(repo_root, 'Unsolved_files')
        os.makedirs(unsolved_dir, exist_ok=True)
        
        src = os.path.abspath(filepath)
        file_basename = os.path.basename(filepath)
        candidate = os.path.join(unsolved_dir, file_basename)
        
        # 检查目标文件是否已存在
        if os.path.exists(candidate):
            # 哈希一致：直接使用现有文件
            if file_hash(src) == file_hash(candidate):
                print(f"File already in Unsolved_files, using: {candidate}")
                return candidate
            # 哈希不一致：生成唯一文件名
            else:
                base, suf = os.path.splitext(file_basename)
                i = 1
                while True:
                    cand = os.path.join(unsolved_dir, f"{base}_{i}{suf}")
                    if not os.path.exists(cand):
                        shutil.copy2(src, cand)
                        print(f"Copied to Unsolved_files (unique name): {cand}")
                        return cand
                    else:
                        if file_hash(src) == file_hash(cand):
                            print(f"File already in Unsolved_files, using: {cand}")
                            return cand
                    i += 1
        # 目标文件不存在：直接复制
        else:
            shutil.copy2(src, candidate)
            print(f"Copied to Unsolved_files: {candidate}")
            return candidate
    except Exception as e:
        print(f"Warning: failed to copy to Unsolved_files: {e}")
        return None

def move_to_tested(unsolved_path):
    """
    将文件从 Unsolved_files 移动到 tested_files 文件夹（避免重复）
    :param unsolved_path: Unsolved_files 中的文件路径
    :return: 移动后的文件路径（None表示移动失败或已存在）
    """
    try:
        repo_root = os.path.dirname(os.path.abspath(__file__))
        tested_dir = os.path.join(repo_root, 'tested_files')
        os.makedirs(tested_dir, exist_ok=True)
        
        file_basename = os.path.basename(unsolved_path)
        dst = os.path.join(tested_dir, file_basename)
        
        # 检查目标文件是否已存在
        if os.path.exists(dst):
            # 哈希一致：删除源文件，返回已存在路径
            if file_hash(unsolved_path) == file_hash(dst):
                os.remove(unsolved_path)
                print(f"Already in tested_files, removed unsolved copy: {dst}")
                return dst
            # 哈希不一致：生成唯一文件名
            else:
                base, suf = os.path.splitext(file_basename)
                i = 1
                while True:
                    candidate = os.path.join(tested_dir, f"{base}_{i}{suf}")
                    if not os.path.exists(candidate):
                        shutil.move(unsolved_path, candidate)
                        print(f"Moved to tested_files (unique name): {candidate}")
                        return candidate
                    else:
                        if file_hash(unsolved_path) == file_hash(candidate):
                            os.remove(unsolved_path)
                            print(f"Already in tested_files as {candidate}, removed unsolved copy")
                            return None
                    i += 1
        # 目标文件不存在：直接移动
        else:
            shutil.move(unsolved_path, dst)
            print(f"Moved to tested_files: {dst}")
            return dst
    except Exception as e:
        # 降级处理：生成唯一文件名强制移动
        try:
            base, suf = os.path.splitext(os.path.basename(unsolved_path))
            i = 1
            while True:
                candidate = os.path.join(tested_dir, f"{base}_{i}{suf}")
                if not os.path.exists(candidate):
                    shutil.move(unsolved_path, candidate)
                    print(f"Moved to tested_files (fallback): {candidate}")
                    return candidate
                i += 1
        except Exception as fallback_e:
            print(f"Warning: failed to move to tested_files: {fallback_e}")
            return None

def write_log_to_file(log, dst_file_path, result, total_elapsed):
    """
    将log统计信息写入txt文件（统计时间总计排除extrct_timer、ctg_timer、inductive_timer）
    :param log: Log类实例，包含统计数据
    :param dst_file_path: tested_files中文件的路径（如 xxx.aig）
    :param result: PDR执行结果（10=UNSAFE, 20=SAFE, 其他=UnSolved）
    :param total_elapsed: 总执行时间（秒）
    """
    # 生成日志文件名（与输入文件同名，后缀改为.txt）
    log_filename = os.path.splitext(os.path.basename(dst_file_path))[0] + ".txt"
    log_file_path = os.path.join(os.path.dirname(dst_file_path), log_filename)
    
    # 定义需要统计的功能列表（名称 -> (计数器属性, 计时器属性)）
    stats_items = [
        ("Block 处理", "block_cnt", "block_timer"),
        ("inductive 操作", "inductive_cnt", "inductive_timer"),  # 保留显示，但不计入总计
        ("generlize 操作", "generlize_cnt", "generlize_timer"),
        ("CTG 处理", "ctg_cnt", "ctg_timer"),  # 保留显示，但不计入总计
        ("propagate 操作", "propagate_cnt", "propagate_timer"),
        ("extract 处理", "extrct_cnt", "extrct_timer"),  # 保留显示，但不计入总计
        ("Pre 处理", "prebad_cnt", "prebad_timer"),
    ]
    
    # 格式化时间（自动适配秒/毫秒/微秒）
    def format_time(seconds):
        if seconds < 0.001:
            return f"{seconds * 1000000:.2f} μs"
        elif seconds < 1.0:
            return f"{seconds * 1000:.2f} ms"
        else:
            return f"{seconds:.2f} s"
    
    # 计算总计信息：排除 extrct_timer、ctg_timer、inductive_timer
    excluded_timers = ["extrct_timer", "ctg_timer", "inductive_timer","generlize_timer"]
    total_calls = sum(getattr(log, cnt_attr, 0) for _, cnt_attr, _ in stats_items)
    total_all_time = 0.0
    for _, _, timer_attr in stats_items:
        if timer_attr not in excluded_timers:
            total_all_time += getattr(log, timer_attr, 0.0)
    
    # 写入文件
    with open(log_file_path, "w", encoding="utf-8") as f:
        # 写入头部信息（注明排除的计时器）
        f.write("=" * 60 + "\n")
        f.write("PDR 算法执行日志\n")
        f.write("=" * 60 + "\n")
        f.write(f"输入文件: {os.path.basename(dst_file_path)}\n")
        f.write(f"执行结果: {'UNSAFE' if result == 10 else 'SAFE' if result == 20 else 'UnSolved'}\n")
        f.write(f"总执行时间: {total_elapsed:.6f} s\n")
        f.write(f"统计时间总计（排除归纳性检查/CTG处理/子句提取）: {format_time(total_all_time)}\n")
        f.write(f"总调用次数: {total_calls}\n")
        f.write("=" * 60 + "\n\n")
        
        # 写入详细统计表格
        f.write(f"{'功能名称':<12} {'调用次数':<8} {'总耗时':<15} {'单次平均耗时':<15}\n")
        f.write("-" * 50 + "\n")
        
        for func_name, cnt_attr, timer_attr in stats_items:
            call_cnt = getattr(log, cnt_attr, 0)
            total_time = getattr(log, timer_attr, 0.0)
            
            # 计算平均时间（避免除零）
            avg_time = total_time / call_cnt if call_cnt > 0 else 0.0
            
            # 格式化输出
            f.write(f"{func_name:<12} {call_cnt:<8} {format_time(total_time):<15} {format_time(avg_time):<15}\n")
        
        f.write("\n" + "=" * 60 + "\n")
        f.write(f"日志生成时间: {time.strftime('%Y-%m-%d %H:%M:%S', time.localtime())}\n")
        f.write(f"备注: 统计时间总计排除了归纳性检查(inductive_timer)、CTG处理(ctg_timer)、子句提取(extrct_timer)的耗时\n")
        f.write("=" * 60 + "\n")
    
    print(f"日志文件已生成: {log_file_path}")




def main(args):
    # 默认文件路径（可通过命令行参数覆盖）
    filepath = "/home/lyj238/wdl/IC3/test.blif"
    filepath = "/home/lyj238/wdl/IC3/pipeLinedAdder_final.blif"
    # filepath = "/home/lyj238/wdl/data/hwmcc15-benchmarks-single-blif-xor/6s173.blif"
    if args:  # 如果传入命令行参数，使用第一个参数作为文件路径
        filepath = args[0]
    
    filename, ext = get_file_extension(filepath)
    print("filename=", filename)
    print("fileext=", ext)
    
    # 1. 复制文件到 Unsolved_files
    # unsolved_path = copy_to_unsolved(filepath)
    # if not unsolved_path and ext in ('.aig', '.aag'):
    #     print("Warning: failed to copy file, continue processing...")


    
    # 2. 执行 PDR 算法
    start_time = time.perf_counter()
    result = -1  # 初始化结果
    log = None

    if ext == '.blif':
        blif = parse_blif_with_layered_vars(filepath)
        result, log = pdr_main(blif)
        
    else:
        print("请输入正确的文件格式（.aig 或 .aag）")
        return
    
    # 输出执行结果
    if result == 20:
        print("The design is SAFE")
    elif result == 10:
        print("The design is UNSAFE")
    else:
        print("UnSolved")
    
    end_time = time.perf_counter()
    total_elapsed = end_time - start_time
    print(f"Elapsed time: {total_elapsed:.6f} seconds")
    
    # 3. 移动文件到 tested_files
    # dst = None
    # if ext in ('.aig', '.aag') and unsolved_path:
    #     dst = move_to_tested(unsolved_path)
    
    # # 4. 生成日志文件（仅当log有效且dst存在时）
    # if log is not None and dst is not None:
    #     write_log_to_file(log, dst, result, total_elapsed)
    # elif log is None:
    #     print("Warning: log is None, skip writing log file")
    # elif dst is None:
    #     print("Warning: destination path in tested_files not found, skip writing log file")

if __name__ == "__main__":
    # 将命令行参数（排除脚本名）传入main函数
    main(sys.argv[1:])