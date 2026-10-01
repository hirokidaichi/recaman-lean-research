# 2026-10-01 研究引き継ぎ

**任意長の最小P2窓について、真の最古Sより古いA末尾長tは
`t≤max(SS数−1,0)`。全SS数で等号を達成する語も構成した。**
E-361、カードH-20261001-01の最終状態は **PROVED-PAPER**。
Lean形式化・独立者の監査は未実施。全射性・一般Gate T6は未解決のままである。

## 今回の成果と根拠

[完全な紙上証明](TERMINAL_A_BUDGET_2026-10-01.md)は、prefixのmassが2以下の
符号語では最初のP2 prefixがSで終わることを示す。mass=1への連続した再訪で、
momentは上側AS往復ではちょうど1減り、下側往復では増える。この事実と
SS数によるsuffix mass下界を組み合わせる。長さ制限や計算結果への依存はない。

最も直接的な帰結は、SS=2の最小donorなら古いA末尾は0個か1個に限られること。
一方、SS数を増やせば末尾長も無限に増やせるので、一律の定数上限は置けない。
最強の根拠はこの全長の証明と明示的な無限族であり、有限計算とは区別する。

計算は `COMPUTED`：discovery 3,021 P2語、長さ23のclaim-specific holdout
30,554 P2語で反例0。うち最小A-ended語はそれぞれ729件、7,895件であり、
前件は空でない。長さ0..11の全4,095語を別の直接和計算で照合し、全34 P2語が一致。
等号族q=0..40も通過した。原出力・実行前ハッシュは
[データ](data/terminal_a_budget_20261001/)に保存した。

## 反例・失敗・適用限界

数学的な修理や反証実験の失敗runはない。意図的な弱化に対しては、最小性を落とすと
`AASASSA`（q=t=1、短いP2 prefixあり）、mass=1を落とすと`ASSA`、
moment=0を落とすと`A`が反例になる。t=0を除外せず狭義不等式を書くと
`AAS`（q=t=0）が反例となる。prefix massの上限を3へ上げても補題は破れる。

既存の未コミットH-05/E-360成果を依存にしていない。証明・反証・形式の照合・意味監査は
同一セッションの別passであり、独立監査と表現しない。紙上証明の読み直しと
既存Lean全体のbuild成功は、この新命題のLean認証ではない。

## 変更範囲と再現

元checkoutの既存変更を保存するため、HEAD
`08c08565c743f39350c9b959e1df7d30aa1cae5d`から隔離したworktreeで作業した。
ブランチは `codex/p2-terminal-tail-bound`。E-360は既存の未コミット研究が使っているため
再利用せず、新結果をE-361とした。元checkoutのファイルはstage/commitしない。

- 新規：仮説カード、完全証明、本引き継ぎ、`experiments/terminal_a_budget.py`、凍結protocol・ハッシュ・JSON結果・検証ログ。
- 更新：`CURRENT_FRONTIER.md`、`EVIDENCE_REGISTRY.tsv`、`PROOF_MAP.md`、`DEVELOPMENT_LOG.md`。
- Leanソース、Audit、protected claims、gate実装には変更なし。

実行コマンド（リポジトリroot基準）：

```bash
shasum -a 256 -c docs/data/terminal_a_budget_20261001/PRE_RUN_SHA256SUMS
python3 experiments/terminal_a_budget.py discovery
python3 experiments/terminal_a_budget.py holdout
bash scripts/check_research_registry.sh
./scripts/check.sh
git diff --check
```

初回の全体検証は新worktreeでのcold buildだった。既存の大きな証明書のうち
DeepNineteenは512秒で通過したが、DeepSixtyoneの再計算が長引いたため、今回の
compilerだけをSIGINTで中断した。初回checkはexit 1（compilerは130）であり、
成功として数えない。[中断ログ](data/terminal_a_budget_20261001/check_cold_interrupted.log)を保存。

その後、元checkoutと対象ソース・全6依存モジュールのソース、依存olean、toolchainが
同一であることを確認し、対象の既存ビルド出力とLake traceを無変更でコピーした。
[比較根拠](data/terminal_a_budget_20261001/cache_provenance.json)を保存し、通常の
`./scripts/check.sh`を再実行した。続くmex証明書も同じtrace全体を再評価するため、
対象を含む9モジュールで同様の一致確認を行い、このcompilerも明示的に中断して
キャッシュを再利用した。2回目もexit 1であり、
[そのログ](data/terminal_a_budget_20261001/check_trace_cache_interrupted.log)を保存した。
3回目が最終検証。hash・gate・検証スクリプトの変更や迂回はしていない。
最終実行はexit 0：**390 jobs、2,549宣言の公理監査、禁止事項走査がすべて合格**。
許可公理は `{propext, Classical.choice, Quot.sound}` の範囲内。
[最終検証ログ](data/terminal_a_budget_20261001/check.log)を保存した。
台帳360件・PROVED-LEAN 154件の同期、G1〜G5、保護された中心命題4件も合格。
新しいE-361はこの154件に含まれず、紙上証明のままである。
実行前ハッシュ照合・資料リンク・集計値・`git diff --check`も合格。
新Leanファイルやgate変更がないため、module lintとgateの負例テストは対象外。

## 次の判断

この作業単位は紙上成果で終了する。次は「prefix mass≤2なら最初のP2はS終了」
の補題と鋭い末尾上界を、同じ量化子のままLean化するのが明確な小課題である。
一般lagを再開するには別途 `delta=r-kx` を拘束する命題と反証gateが必要。
今回制限できたのは `t=L-r` だけで、`L-kx=delta+t` のdelta側は未解決。
探索上限の延長や旧lag-15証明書ルートの再開には進めない。
