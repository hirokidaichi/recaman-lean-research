# R-20261022-MAKEUP 再現資料

結論・仮定・次の判断は[引き継ぎ](../../RESEARCH_HANDOFF_2026-10-22_MAKEUP.md)、
各runの実行前仕様は[PROTOCOL](PROTOCOL.md)を参照する。最初の凍結版は[PROTOCOL.initial.md](PROTOCOL.initial.md)。
本folderのCOMPUTED結果を一般Qの証明へ昇格させない。

## 何を固定したか

- revision.txtは開始時HEAD。追跡済みdirty状態はdirty.patch、最終状態はfinal-dirty.patchに保存。
- 各*.meta.jsonはargv/上限/目的/source SHA。RUN_INDEX.tsvはそのcommand一覧。
- 各*.jsonは正確な結果。*.timeは/usr/bin/time -lのraw出力、solverは*.model.pbtxtと*.solver.logも保存。
- source-hash-audit.jsonは22件の実行source/model hash照合。元PROTOCOLのhashに合うappend前prefixも復元した。
- source-snapshot.zipとそのmanifestは、検証時のLean全sourceと工具419ファイルの読取snapshot。
  evidence-snapshot.zipは台帳・逐語監査・frontier・紙上結果を収め、両archiveを一時directoryへ展開してG5/lint/protected/briefを通した（isolated-snapshot-check.json）。
  他セッションの既存変更も含むため、全てを今回の著作・修正・commitと主張しない。
- solver-requirements.txt、solver-install-report.json、tool-versions.jsonは実行環境。
- SHA256SUMSは本folderの各artifactの最終hash。自分自身を含めない。

## 短い独立検証

repository rootから実行する。以下は新しい探索上限の設定ではなく、保存済みの領域の再検証。
出力を再生成すると時刻/solve統計が変わるため、元のraw出力を先に別の場所へ保存して比較する。

```sh
python3 scripts/harness_gate.py --lint-module Recaman/BlockSuffixPositivity.lean
./scripts/check.sh
make test-tools
make brief
recaman_audit_dir=$(mktemp -d /tmp/recaman-audit-XXXXXX)
cp docs/data/c1_q_makeup_20261022/contexts.json docs/data/c1_q_makeup_20261022/context-classify.json "$recaman_audit_dir/"
python3 docs/data/c1_q_makeup_20261022/context_audit.py docs/data/c1_q_makeup_20261022/contexts.json --out "$recaman_audit_dir/context-language.json"
python3 docs/data/c1_q_makeup_20261022/context_tree_audit.py --directory "$recaman_audit_dir"
python3 docs/data/c1_q_makeup_20261022/prefix_mass_audit.py --max-mass 17 --out "$recaman_audit_dir/prefix-language.json"
python3 docs/data/c1_q_makeup_20261022/spectrum_formula_audit.py
```

C++はC++17、-O3でbuildした。RUN_INDEX.tsv内の/tmp binary名に対応するsourceは
area_probe.cpp、area_probe_v2.cpp、holdout.cpp、budget_classify.cpp、context_classify.cpp、
prefix_mass_search.cpp、prefix_mass_independent.cpp。各metadataのsource名を優先する。
一例:

```sh
c++ -std=c++17 -O3 docs/data/c1_q_makeup_20261022/prefix_mass_independent.cpp -o /tmp/recaman-c1-prefix-mass-independent
/usr/bin/time -l /tmp/recaman-c1-prefix-mass-independent 32 17 300
```

この独立版はG式・mod4削減を使わず、全始点の後ろ向きmass/moment、全levelの直接面積和を使う。
prefix-mass-independent-comparison.jsonが元の全125181373 nodeとの一致を記録している。

## ソルバの再現

OR-Toolsは隔離venvへinstallし、version 9.15.6755と依存versionを保存した。
/tmp/recaman-c1-solver-20261022/bin/pythonは当日作成したvenvのpathであり、将来は新しいvenvへ置き換える。
各modelの意味と安全な整数domainは[MODEL_DOMAIN_AUDIT.md](MODEL_DOMAIN_AUDIT.md)。
校正modeと実行modeの引数はsourceの--helpおよび*.meta.jsonを参照する。

UNKNOWNの900秒runを同じ予算で繰り返すことを、次の研究unitの推奨とはしない。
今回はR-negative/peak-five/deep-three/Y-triangleをUNKNOWNで停止し、目的も実行時間も延長しなかった。
sourceのcommon_prefix_lift.pyはspectrum緩和がSATだった場合の条件付き監査用。
今回の緩和はINFEASIBLEだったため、持上げ探索は実行していない。

## discoveryとholdoutの範囲

discovery-20-32と28-64は以前の研究で見た短い構造を含むため、未使用holdoutではない。
holdoutは2百万の新しい完全語、長さ80..384の8生成群を凍結した一回のrun。
短いmotifやprefixの全てが未使用だとは言わず、全長384の網羅や一様分布とも呼ばない。
有限分類・solver・holdoutはそれぞれ別の証拠で、相互の数字を合算して確信度に変換しない。

## 費用と証拠label

cpu-accounting.jsonはtimeログのあるrunのuser+sys合計3425.57秒。
この値は経過研究時間に足さない。全てのcompiler/Lean/installのCPUを測った総CPUではない。
E-379〜E-381はPROVED-LEAN、E-382/E-383はCOMPUTED、E-384はPROVED-PAPER。
E-384の存在方向と有限分類のkernel証明書化、a_z≤3の一様な深さ供給は別の未実施義務。
Q/C1/H/SLと中心命題のlabelは変更していない。
