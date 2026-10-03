# 02:30 writer commands and outputs

cwdは全て `/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`。
短いread-only照合のみで外部timeoutなし。toolのyieldは処理timeoutではない。

1. 開始時に `date`, `git rev-parse HEAD`, `git status --short`, `rg --files` を一つのread-only shellで実行。
   - date `2026-09-24 02:32:04 JST`
   - HEAD `08c08565c743f39350c9b959e1df7d30aa1cae5d`
   - dirty一覧は `raw/start_state.txt` に要約保存。既存dirtyを保持。
2. `wc -l ...; find docs/data/issue73_20260924 ...; find docs/adversarial_audits ...`
   - 必須資料と01:00/01:30/02:00 packet・監査の所在を確認。exit 0。
3. `cat` / `rg -n` / `head` / `tail` による必須資料、元signature、candidate、監査の読取。
   - 新しい数学判断なし。参照先は `candidate_packet.md` に固定。
4. `shasum -a 256 -c docs/adversarial_audits/H-20260917-01_20260924_0200_PARENT_SHA256SUMS`
   - 25/25 `OK`、exit 0。完全stdoutは `raw/parent_manifest_verify.stdout`。
5. `shasum -a 256 docs/RESEARCH_WEEKLY_REPORT_2026-09-24.md docs/HYPOTHESIS_CARD_2026-09-17_SHORT_TIGHT_DONOR_AVOIDANCE.md docs/RESEARCH_HANDOFF_2026-09-24_SOL.md`
   - 週報 `00b149...7dfd9d2`、主カード `7f73cc...078b479`、handoff `1846cf...c939d13c`。
6. `ps -axo pid=,ppid=,etime=,command= | rg 'issue73_20260924|matching_closure|baseline_q_w|SS2OldestPattern|ShortTightDonorAvoidance|harness_gate.py|scripts/check.sh' || true`
   - shellとrg自身以外の一致0。automation停止確認ではない。
7. `mkdir -p .../slot0230/raw` と `cp -p` でlive 3文書のoriginal/full候補を機械的複製。
8. `apply_patch` で追記draft、full候補、packet、commands/raw記録を作成。
9. 親から02:33:23 JSTのautomation停止・再読確認と証跡hashの通知を受領し、`apply_patch` で候補へ反映。
10. 最終検証の逐語sourceは `raw/final_validation.sh`。実行argvは
    `zsh docs/data/issue73_20260924/slot0230/raw/final_validation.sh`。stdout/stderr/exitは同名rawへ保存する。

執筆者は今枠で `report_vacuity.py`、`harness_gate.py`、Lean build、`./scripts/check.sh`、実験・探索を実行していない。
独立者のH-04既知literal再計算は監査担当の実行であり、このwriter commandsには含めない。
01:00/01:30に記録されたvacuity/lint/check結果は同版旧原ログであり、今回実行としない。
