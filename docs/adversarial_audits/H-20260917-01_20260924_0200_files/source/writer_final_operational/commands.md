# 02:00 writer commands

- cwd: `/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`
- HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`
- command timeout: 読取コマンドは短時間で終了し、外部`timeout`は付けていない。toolの10秒`yield`は
  timeoutではない。長時間処理なし。
- 新計算、Lean build/lint/check、探索範囲延長は実行していない。

実行した読取・保存コマンド:

```sh
date '+%Y-%m-%d %H:%M:%S %Z'
git rev-parse HEAD
git status --short
sed -n ... <必読文書・全週間カード・各日handoff・監査記録>
rg -n ... <GLOSSARY/PROOF_MAP/RESEARCH_PORTFOLIO/EVIDENCE_REGISTRY/CURRENT_FRONTIER>
cp -p <週報・主カード・handoff> docs/data/issue73_20260924/slot0200/<凍結名>
rg -n '^(theorem|lemma|def) ' Recaman/SS2OldestPattern.lean
```

開始実時計: `2026-09-24 02:03:07 JST`。
凍結実時計: `2026-09-24 02:04:22 JST`の直後。正確な値は`raw/freeze_time.txt`。
開始時git statusとrevisionは`raw/`に保存した。読取検索結果は`raw/pending_search.txt`、
H-05 symbol一覧は`raw/ss2oldest_symbols.txt`。stdoutが長い検索は画面表示が切れたため、保存rawを正本とする。
source hash・対象protocolは実行前に確認し、stdoutは実行後にrawへ保存した。両者を同時刻の事前凍結とは書かない。

手修正は`apply_patch`のみ。byte保存用の`cp -p`以外で既存ファイルを変更していない。

## 独立判定と最終検証

独立監査は、candidate
`e68be6a79dfa42ff4069357bfbe0899c0333636dd216f39bbc04bac05a42ce34`、weekly full
`00b149ea96eafdddcbfbe4a4e09031ca0779ab1ffdfd93fa941d02bb57dfd9d2`、card full
`7f73cc1ec105e699b571e5f0df78d5ddcef670dc304f44a9d5df9efee078b479`、handoff
`6f1be22eacc70b30871035d737f9c49f97c06e2967e75240c0788ae9f977301d`を対象に限定合格。
独立報告SHAは`17c388cc98cfb4924fee355db10d632087cd60e2b82e20d2a8aa11949dd6d011`、
初期manifest SHAは`5ca667280a36cb395275f8f437da90e3e1899dcf9037501b52d21036e6a2735f`、123/123 OK、exit 0。

最終fullの構成確認は、各freezeのbyte数を使ってprefixと、区切りの改行1byte後のsuffixを分離した。

```sh
wbytes=$(wc -c < docs/data/issue73_20260924/slot0200/original_weekly_report_at_freeze.md)
cbytes=$(wc -c < docs/data/issue73_20260924/slot0200/original_main_card_at_freeze.md)
head -c "$wbytes" docs/data/issue73_20260924/slot0200/proposed_weekly_report_full.md > docs/data/issue73_20260924/slot0200/raw/weekly_full_prefix.check
tail -c +$((wbytes+2)) docs/data/issue73_20260924/slot0200/proposed_weekly_report_full.md > docs/data/issue73_20260924/slot0200/raw/weekly_full_suffix.check
head -c "$cbytes" docs/data/issue73_20260924/slot0200/proposed_main_card_full.md > docs/data/issue73_20260924/slot0200/raw/card_full_prefix.check
tail -c +$((cbytes+2)) docs/data/issue73_20260924/slot0200/proposed_main_card_full.md > docs/data/issue73_20260924/slot0200/raw/card_full_suffix.check
cmp docs/data/issue73_20260924/slot0200/original_weekly_report_at_freeze.md docs/data/issue73_20260924/slot0200/raw/weekly_full_prefix.check
cmp docs/data/issue73_20260924/slot0200/weekly_report_append_draft.md docs/data/issue73_20260924/slot0200/raw/weekly_full_suffix.check
cmp docs/data/issue73_20260924/slot0200/original_main_card_at_freeze.md docs/data/issue73_20260924/slot0200/raw/card_full_prefix.check
cmp docs/data/issue73_20260924/slot0200/main_card_append_draft.md docs/data/issue73_20260924/slot0200/raw/card_full_suffix.check
```

4件の`cmp`は全てexit 0、stdout/stderr空。`git diff --check -- docs/data/issue73_20260924/slot0200`
もexit 0、stdout/stderr空。最終freeze時刻とこれらの未加工結果は`raw/final_validation.*`へ保存する。

- 最終本文・監査metadata freeze: `2026-09-24 02:19:59 JST`。
- 最初のvalidation wrapperはzshのread-only変数`status`へ代入して末尾で失敗した。検査本体の原出力を
  `raw/final_validation.v1.*`へ保持し、変数名を`run_exit`へ直して同じ検査を再実行した。
- 修正版wrapperはexit 0。失敗版を成功へ書き換えず、最終manifestに両方を含める。
