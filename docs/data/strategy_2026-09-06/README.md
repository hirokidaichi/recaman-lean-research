# 2026-09-06 strategy audit: reproducibility

Base revisionとworking-tree source hashesは `source_hashes.txt`。
既存canonical recurrence、discovery/holdout境界、停止条件は各hypothesis cardに固定した。
`seeded_witness.json` と `prefix_witness.json` は最終seed、全符号語、exact trace、arc completionを含む。
一般族の数学的主張はfinite replayの外挿ではなく `STRATEGY_AUDIT_2026-09-06.md` の紙上証明による。

```sh
python3 experiments/escape_quantifier_audit.py
python3 experiments/seeded_survival_falsifier.py --out /tmp/seeded_witness.json
python3 experiments/prefix_survival_stress.py --out /tmp/prefix_witness.json
python3 experiments/survival_countermodel_family.py

c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/preload_free_survival_probe.cpp -o /tmp/preload_free_survival
/tmp/preload_free_survival 2000000 20000 900 /tmp/canonical_records.txt

c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/arc_death_rule_probe.cpp -o /tmp/deathrule
mkdir -p /tmp/weighted_drop_2e10
/tmp/deathrule 20000000000 /tmp/weighted_drop_2e10
python3 experiments/weighted_landing_drop.py /tmp/weighted_drop_2e10/comb_ends.txt

mkdir -p /tmp/weighted_drop_first
/tmp/deathrule 11685741478 /tmp/weighted_drop_first 11685044246 11685741478
python3 experiments/weighted_drop_trace_audit.py /tmp/weighted_drop_first/trace.txt
python3 experiments/weighted_drop_birth_probe.py

./scripts/check.sh
```

Generalized probeのz=0出力は、既存death-rule probe 2Mから
`T=1,hasRun,blocked,continued,arcCompleted` の全59行を抽出し、
`(c,v,J,hPrev,c+gap)` と完全一致することを確認した。
残りのzをcanonicalと呼ばない。事前historyは0と単一初期値のみで、途中のpreloadはない。

実装時の修正: `prefix_survival_stress.py` のvが既知Fにある場合は、prefix自体を生成できないので
`PREFIX_INCOMPATIBLE` として記録する。これは探索nodeを完走した結果とは区別する。
最初の探索呼出しではこの場合をassertで停止し、recordの扱いを明示して再実行した。
またcanonical record比較は書込み中のbufferを読む呼出しを避け、別の完走したz=0実行と照合した。

H-08のweighted候補はholdoutで5反例を得たためREFUTED、係数修正なしで停止した。
`weighted_landing_drop.txt` は全適用行の集計、`weighted_drop_counterexample_rows.txt` は
5反例と対応する次combの原表行、`canonical_20B_checks.txt` は元simulatorのguards。
全comb tableと697,233行のtraceは上のコマンドで再生成でき、hashを出力へ保存している。
大きい中間tableを証明書として扱わない。

`weighted_drop_first_trace.txt` と `weighted_drop_boundary_births.txt` は反証後の原因診断。
既存run-length simulatorでは監視値7個のみを一時コピーで差し替え、漸化式・加速ロジックは変更しない。
これは新候補のholdoutではなく、固定した最初の反例の再現である。birth値の監視にも加速sectionの
閉形式が使われる。最終値は非加速の一歩ずつのsimulatorと一致した。
