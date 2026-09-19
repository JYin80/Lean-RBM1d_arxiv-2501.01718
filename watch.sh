#!/usr/bin/env bash
# 在一个备用终端里跑： ./watch.sh
# 它监视源码改动并自动 lake build，把结果写进 build.log（Claude 直接读）。
# Ctrl-C 退出。
cd "$(dirname "$0")" || exit 1
touch -t 200001010000 build.log 2>/dev/null || :
echo "watching RBM1D/ ... (Ctrl-C to stop)"
while sleep 3; do
  changed=$(find RBM1D RBM1D.lean lakefile.toml -newer build.log 2>/dev/null | head -1)
  if [ -n "$changed" ]; then
    echo "--- rebuild $(date +%T) ---"
    ./check.sh > /dev/null 2>&1
    grep -c "^error:" build.log 2>/dev/null | sed 's/^/  errors: /'
  fi
done
