#!/usr/bin/env bash
# 在 macOS 终端里跑： ./check.sh
# Claude 会直接读同目录下的 build.log，你不用贴任何东西。
cd "$(dirname "$0")" || exit 1
{ echo "=== $(date) ==="; } > build.log
lake build >> build.log 2>&1
code=$?
echo "=== lake build exit=$code ===" >> build.log
grep -c "error:" build.log 2>/dev/null | sed 's/^/errors: /' >> build.log
tail -n 20 build.log
