# 02:00 枠 worker report

## 結論

**`INCOMPLETE`。W_partial の具体反例も、受入可能な有限0件結果も得ていない。**
修正版は p=1..11 の正質量周期語1,872件を完走したが、Hall を満たす proper U 上の
w1 antecedent が0件だった。入口契約は対象0件を成功にしないため、program が表示した
`EXHAUSTED_ZERO` を証拠判定として採用せず手動で降格する。元 W/Q は `CONJECTURED` のまま。

## Hypothesis card status

- 元カード Q/W: `CONJECTURED`、変更なし。
- 今回の弱化 `W_partial`: 未判定。反例なしを主張しない。
- 有限出力: target 非空性を満たさなかった `OBSERVED` 診断。ただし成果昇格なし。

## 実行

HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`。

初回 source SHA256:
`ead649739e53ca1d52853cac01f11a47f957b1ee1320469849971a5560cdbac5`。

```sh
python3 -u experiments/issue73_20260920/w_partial_u_probe.py --max-period 11 --max-work 2000000 --seconds 240
```

初回 exit 0、runner wall 5.738032秒、program elapsed 5.576564秒。正質量語1,872、
tight B 2,202、表示 antecedent 0。antecedent を next=S まで含めて数える実装誤りのため拒否。
原出力は `worker_raw_v1.jsonl`、理由は `repair_note.md`。

一回だけの修正版 source SHA256:
`d3fc203ba3c42f24000b15dce119f83d016fd7a6fb6d4aa65039327433475a94`。
command は同じ。exit 0、runner wall 5.611630秒、program elapsed 5.664199秒。

```text
positive_words=1872
completed_positive_words=1872
tight_b_examined=2202
incomplete_u_examined=0
w1_antecedents=0
work=0
status printed by program=EXHAUSTED_ZERO
worker evidence decision=INCOMPLETE
```

修正版は antecedent と next=S を分離したが、antecedent を持つ tight B を含む proper U が
列挙されず、受入契約の `w1_antecedents >= 1` を満たさなかった。source がこの非空性条件を
終了 status に反映せず `EXHAUSTED_ZERO` と表示した点も残る。修理枠を使い切ったため追加修正しない。

## 強い事実と限界

- inclusive `1 <= d <= p(p+1)`、全正質量語、全 tight short B の走査自体は完了表示された。
- 既知 full-U 集計と同じ tight B 2,202 を再現した。
- proper U 上の適用対象が0だったため、full Supp/Hall の分岐、具体 witness、全前提と結論否定の
  二実装再計算は発火しなかった。
- program の control flow から `incomplete_u_examined=0` は、w1 antecedent を持つ tight B に対し
  full Supp 以外の U が検査対象へ到達しなかったことを示すが、独立再計算前なので数学的な有限除外へ
  昇格しない。
- representative t から全 Int t への周期移送も独立監査未完了。従って一般 W、全p、元Wの成立を
  結論しない。

## 変更ファイル

- `experiments/issue73_20260920/w_partial_u_probe.py`
- `docs/data/issue73_20260920/slot0200/entry_proposal.md`
- `docs/data/issue73_20260920/slot0200/worker_raw_v1.jsonl`
- `docs/data/issue73_20260920/slot0200/worker_raw_v2.jsonl`
- `docs/data/issue73_20260920/slot0200/repair_note.md`
- 本報告と `SHA256SUMS`

旧 gate、カード、引継ぎ、plan、registry、frontier、proof map、Lean、harness は変更していない。

## 失敗、残義務、次判断

失敗は二つ: 初回の antecedent 誤計数と、修正版の target 0 を成功 status にした非空性判定不足。
二回目の修理、別名実装、範囲拡大で延命しない。

独立監査は、raw/source hash と target 0 の意味を確認し、この枠を `INCOMPLETE` として閉じるかを
判定する。再開するなら新しい枠で、proper U 上にも w1 antecedent が実在する既知例を先に与えるか、
「target 0 の有限分類」を別の一問・受入契約として事前凍結する必要がある。本枠ではどちらも行わない。

Lean 変更・新規定理・registry 行がないので vacuity report、module lint、`check.sh` は対象外で、
実行済みとは主張しない。
