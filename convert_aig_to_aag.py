#!/usr/bin/env python3
"""
批量将 AIG 文件转换为 AAG 格式的脚本
使用 ABC 工具进行转换
"""

import os
import subprocess
import sys
from pathlib import Path

def convert_aig_to_aag(aigtoaig_tool, input_file, output_file):
    """
    使用 aigtoaig 工具将 AIG 文件转换为 AAG 格式
    """
    try:
        # 构造 aigtoaig 命令
        cmd = [aigtoaig_tool, input_file, output_file]
        
        # 执行转换
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
        
        if result.returncode == 0:
            return True, "成功"
        else:
            return False, result.stderr if result.stderr else "未知错误"
    except subprocess.TimeoutExpired:
        return False, "超时"
    except Exception as e:
        return False, str(e)

def main():
    # 配置参数
    input_dir = "/home/lyj238/wdl/data/hardproblems"
    output_dir = "/home/lyj238/wdl/data/hardproblems_aag"
    aigtoaig_tool = "/home/lyj238/wdl/IC3/aigtoaig"
    
    # 验证输入目录
    if not os.path.isdir(input_dir):
        print(f"错误: 输入目录不存在: {input_dir}")
        sys.exit(1)
    
    # 验证 aigtoaig 工具
    if not os.path.isfile(aigtoaig_tool):
        print(f"错误: aigtoaig 工具不存在: {aigtoaig_tool}")
        sys.exit(1)
    
    # 创建输出目录
    os.makedirs(output_dir, exist_ok=True)
    
    # 获取所有 AIG 文件
    aig_files = sorted(Path(input_dir).glob("*.aig"))
    
    if not aig_files:
        print(f"警告: 在 {input_dir} 中未找到 .aig 文件")
        sys.exit(0)
    
    print(f"找到 {len(aig_files)} 个 AIG 文件")
    print(f"输出目录: {output_dir}")
    print("-" * 60)
    
    success_count = 0
    failed_count = 0
    failed_files = []
    
    for i, aig_file in enumerate(aig_files, 1):
        aag_file = os.path.join(output_dir, aig_file.stem + ".aag")
        
        print(f"[{i}/{len(aig_files)}] 转换: {aig_file.name}", end=" ... ")
        sys.stdout.flush()
        
        success, message = convert_aig_to_aag(aigtoaig_tool, str(aig_file), aag_file)
        
        if success:
            print("✓ 成功")
            success_count += 1
        else:
            print(f"✗ 失败: {message}")
            failed_count += 1
            failed_files.append(aig_file.name)
    
    print("-" * 60)
    print(f"\n转换完成!")
    print(f"成功: {success_count}/{len(aig_files)}")
    print(f"失败: {failed_count}/{len(aig_files)}")
    
    if failed_files:
        print(f"\n失败的文件:")
        for f in failed_files:
            print(f"  - {f}")

if __name__ == "__main__":
    main()
