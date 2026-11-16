# 自動研究ツールの試行（2026-11-16）

[調査レポート](../../docs/AUTO_RESEARCH_TOOL_SURVEY_2026-11-16.md) の「試行」節の再現用一式。
どれも研究ツールの評価であり、**数学的証拠ではない**。台帳・Lean ライブラリには触れていない。
T2（文の固定）と T3（空虚性プローブ）は同日に本線化した。正本は `docs/protected_pins/`、`scripts/harness_lean.py`、
`scripts/lean/` で、ここにある版は試行時の記録。
基準 revision は `82ad51a`（Lean v4.33.1、ビルド済み `.lake` を使用）。

| 試行 | 中身 | 再現コマンド（repo root から） | 結果 |
|---|---|---|---|
| T1 反例探索ベンチ | 予想 H（E-509）の評価器 `hmargin.c` と、探索戦略を同じ評価回数で比べる `bench.py` | `python3 experiments/autoresearch_trial_20261116/hmargin.py`（自己テスト）<br>`cd experiments/autoresearch_trial_20261116 && python3 bench.py strategies/anneal.py --budget 5000000 --seeds 2 --tasks rediscover` | 乱択・焼きなまし・ブロック語彙の3戦略とも、500万評価×2 seed で長さ34の H+ 反例（E-511）を再発見できず（`results/bench_baselines.jsonl`） |
| T2 文の固定 | Comparator と同じ考え方を repo 内で実装。人間が書いた `Prop` を、引用された定理が証明するか `exact`/`implies` の2方式で検査 | `python3 experiments/autoresearch_trial_20261116/statement_pin/check_pins.py` | 12/12 が期待どおり。E-510 を E-070 の根拠に引くと `LineCapacity e` が閉じずに拒否（`results/statement_pin.txt`） |
| T3 空虚性プローブ | 証明項レベルで未使用仮定・結論＝仮定・仮定の矛盾・純算術を検査する Lean メタプログラム | 下記 | 固定悪例 5/5 検出、実定理 67 本中 2 本検出（どちらも本当に未使用の仮定）（`results/vacuity_probe_real_modules.txt`） |
| T4 leanchecker | ツールチェーン同梱のカーネル再検査 | `lake env ~/.elan/toolchains/leanprover--lean4---v4.33.1/bin/leanchecker Recaman.CleanWindowCapacity`（`--fresh` で依存も再検査） | 1 モジュール 0.9 秒、`--fresh` 36 秒。全ライブラリ `--fresh Recaman` は exit 0・780 秒・最大 35.5GB |

第 2 段（外部ツール、広木さんの承認後に実施）:

| 試行 | 中身 | 再現コマンド | 結果 |
|---|---|---|---|
| T5 lean-lsp-mcp v0.33.0 | MCP クライアント `lean_lsp_mcp/client.py` から `uvx lean-lsp-mcp` を起動 | `uvx --from lean-lsp-mcp python experiments/autoresearch_trial_20261116/lean_lsp_mcp/client.py list` | goal・verify・局所検索は動作。最小仮定検査は `hkU` を新たに検出した一方、E-720 の `hhb` を呼び出し側の破綻のせいで誤って「必要」と判定（`results/lean_lsp_mcp_*.jsonl`） |
| T6 OpenEvolve 0.4.1 | 探索戦略を `claude -p`（sonnet）で進化、評価器は固定、候補は `sandbox-exec` 内で実行 | `uv venv` に `openevolve` を入れて `evolve/run_openevolve.sh <venv> <out> 16` | 16 反復（233 秒）の最良戦略 `strategies/evolved_run16.py` は、未使用 seed で長さ 34 の既知 H+ 反例を 30 万評価 5/10・100 万評価 8/10 で再発見。焼きなましは 0/10（`results/openevolve_holdout.txt`、`results/openevolve_run16_log.txt`） |

T3 の実行:

```bash
D=experiments/autoresearch_trial_20261116/vacuity_probe
mkdir -p $D/build && lake env lean -o $D/build/VacuityProbe.olean $D/VacuityProbe.lean
LEAN_PATH="$(lake env printenv LEAN_PATH):$PWD/$D/build" lake env lean $D/Fixtures.lean
LEAN_PATH="$(lake env printenv LEAN_PATH):$PWD/$D/build" lake env lean $D/RealModules.lean
```

## 注意

- `hmargin.c` の窓判定は `experiments/issue73_20261020/eqcheck.c` と同じ式。自己テストは長さ ≤ 14 の全語で margin ≤ 0、
  ランダム 300 語で独立な素朴実装と一致、E-511 の語で e = 11・S = 13・unclean = 3 を確認する。
- ベンチの `hunt` タスクはまだ E-372（窓長 ≤ 31 なら H が成立）を目的関数に入れていない。
  H の反例には長さ 32 以上の窓が必須なので、LLM 進化の試行前にそこを直す。
- `vacuity_probe` の `unused` は証明項に仮定の自由変数が現れないことを見る保守的な判定で、
  委譲・η 簡約された証明は「使用」と数える。`shallow` は情報表示のみで、`objects=false` と重なった時だけフラグにする。
