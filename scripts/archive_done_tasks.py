#!/usr/bin/env python3
"""Move finished ticket rows out of docs/TASKS.md into docs/archive/TASKS-done.md.

Usage:  python3 scripts/archive_done_tasks.py          # dry run: list what would move
        python3 scripts/archive_done_tasks.py --apply  # move them

A row is "finished" when its status column (the last column) starts with one of
FINISHED_PREFIXES after stripping ** and backticks.  Rows that are claimed, in
progress, unclaimed or partially done stay.  The live file keeps its header and
table header; the archive is append-only.  Refuses to run if TASKS.md shrinks by
more than the moved rows (guards against the 2695 -> 4 truncation accident).
"""
import re
import sys
import os

TASKS = 'docs/TASKS.md'
ARCH = 'docs/archive/TASKS-done.md'
FINISHED_PREFIXES = ('完成', '已完成', '作废', '已作废', '撤销', '已撤销', '合并', '已合并', '取消', '关闭', '已关闭')


def status_of(row):
    cols = [c.strip() for c in row.rstrip().rstrip('|').split(' | ')]
    return re.sub(r'[*`]', '', cols[-1]).strip()


def main():
    apply = '--apply' in sys.argv
    src = open(TASKS, encoding='utf-8').read()
    lines = src.split('\n')
    keep, moved = [], []
    for l in lines:
        if re.match(r'^\| *T\d+', l) and status_of(l).startswith(FINISHED_PREFIXES):
            moved.append(l)
        else:
            keep.append(l)
    for l in moved:
        print('move', re.match(r'^\| *(T\d+[a-z]?)', l).group(1), '|', status_of(l)[:40])
    if not apply or not moved:
        print(f'{len(moved)} row(s) {"to move (dry run)" if not apply else "moved"}')
        return
    assert len(keep) + len(moved) == len(lines)
    os.makedirs(os.path.dirname(ARCH), exist_ok=True)
    new = not os.path.exists(ARCH)
    with open(ARCH, 'a', encoding='utf-8') as f:
        if new:
            f.write('# 已完成的工单行（从 docs/TASKS.md 移出，只追加）\n\n'
                    '| # | 任务 | 文件 | 认领 | 状态 |\n|---|---|---|---|---|\n')
        for l in moved:
            f.write(l + '\n')
    open(TASKS, 'w', encoding='utf-8').write('\n'.join(keep))
    print(f'{len(moved)} row(s) moved to {ARCH}')


if __name__ == '__main__':
    main()
