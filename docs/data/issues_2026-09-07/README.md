# #70 / #71 reproducibility — 2026-09-07

#70のbaseは8a4314d7、完成commitはf05ddcb。#71のbaseはf05ddcb。
各source hashとexact出力をこのdirectoryに保存した。finite computationは一般証明ではない。

```sh
python3 experiments/survival_family_boundary_audit.py
./scripts/check.sh

python3 experiments/joint_birth_diagnostic.py --out docs/data/issues_2026-09-07
python3 experiments/joint_birth_scalar_check.py --out /tmp/issue71-scalar-birth
python3 experiments/joint_birth_classify.py \
  --births docs/data/issues_2026-09-07/issue71_births.tsv \
  --scalar /tmp/issue71-scalar-birth --out docs/data/issues_2026-09-07
python3 experiments/weighted_drop_trace_audit.py /tmp/issue71-scalar-birth/trace.txt
```

`joint_birth_diagnostic.py`は元のrun-length simulatorの監視対象と出力だけを変更する。
plain 20,000 / targets1..4000で3,789 first birthが一致し、固定対象では加速開始点
2,097,152と3,000,000の全birthが一致した。31,058個のWと境界4個の計31,062値を保存した。
`joint_birth_scalar_check.py`は別の一歩ずつのsimulatorにO(1)の監視器を追加し、全Wを認証した。
どちらも漸化式・membership・加速停止条件・arc判定は変更しない。

追加の観測器なしの回帰対照も実行した:

```sh
mkdir -p /tmp/issue71-scalar
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/arc_death_rule_probe.cpp -o /tmp/issue71-deathrule
/tmp/issue71-deathrule 11685741478 /tmp/issue71-scalar 11685044246 11685741478
cmp /tmp/issue71-scalar/trace.txt /tmp/issue71-scalar-birth/trace.txt
cmp /tmp/issue71-scalar/arcs.txt /tmp/issue71-scalar-birth/arcs.txt
```

両cmpは一致。697,233行のtrace hashは前回H-08診断と同一の
`3908a9358accf069ae3a94238b8faf29f086d5f26d44305c5a92f7fccc6fba4f`。
大きいtraceは上のコマンドで再生成し、このdirectoryにはhash・検査結果・全birthのTSVを保存する。
`issue71_scalar_births.tsv`はi順の独立first birth、`issue71_births.tsv`は値順のproducer segment情報。
`issue71_groups.json`は二つの共有runと値域の完全な要約。
stdoutのelapsedは機械依存だが、birth table、arc table、traceの数値はexactである。

#71の結果は新仮説のholdoutではなく、反証後に対象を固定した原因診断。
一般の資源不等式を発見したとは主張しない。継続判断はH-20260907-02 / E-059でSTOPPED。
