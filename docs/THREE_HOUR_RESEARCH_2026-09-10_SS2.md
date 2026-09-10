# 2026-09-10：SS=2 先頭 run の3時間研究

**境界例 `AAASSSASASA` を通る共通履歴は、S-ended prefix の延長ではなく、先頭 A run の clean 兄弟である。** 名前付き4課金は棄却。全 lag の E-067 / E-070 と全射性・非全射性は未解決。

- 基準 HEAD：`dfbd8444ccc3d0398159917dad3feb5992d1d0b8`。
- 入力：E-128 / E-130 / E-131 の次 unit。「canonical step-115 を通る新しい共通履歴の不等式。なければ型表を足さない」。
- 現在状態の正本：[CURRENT_FRONTIER](CURRENT_FRONTIER.md)。

## 問いと判定

H-30 は、SS=2 最小窓を oldest-S へ送り E-128 と共同で S へ単射できるか、だった。
合格条件は stream 定理か最小反例。停止は名前付き4課金がすべて壊れ、境界例を通る別の不等式もないこと。

| 主張 | 判定 |
|---|---|
| oldest-S は SS=2 最小源のあいだで単射 | `REFUTED`、周期16 |
| first-SS は単射 | `REFUTED`、周期13 |
| newest-S は SS=2 のあいだで単射 | 周期18まで違反0、ただし |
| newest-S は E-128 と交わらない | `REFUTED`、標準 114/113 自身 |
| 最小 P2 で lag>3 なら先頭 AAS 禁止 | `PROVED-LEAN` |
| 先頭 A run a≥3 なら同じ run に clean lag-3 兄弟 | `PROVED-LEAN` |
| 標準 114 はその実例（兄弟 113） | `PROVED-LEAN` |
| SS=2 最小源は A run あたり高々1 | `COMPUTED`（10^7 と周期1..18）、一般証明ではない |

## 反証の要点

周期16の oldest-S 衝突は `AAAASAASASASASSS` 上で、lag11 の `AAASSSASASA` と lag19 の
`SASASAASAAAASSSASAS` が同じ oldest S を共有する。SAAS を含む。E-130 の境界語が片側。

newest-S の自己衝突は周期18まで0で、A run あたり SS=2 は高々1に見える。しかし newest-S は
**同じ run の lag-3 源の E-128 端点**である。標準 sign 114 の窓は先頭 AAA のあと S で、
sign 113 の最小窓は AAS、共通の S は時刻 110。境界例は例外ではなく、この衝突の最小実例。

A 終端の最小 SS=2 語は長さ23まで trailing A が常に1。一方、任意 SS の最小 P2 は
`AAASSASSSAA`（SS=3）のように AA で終わり得る。trailing A=1 を SS 非依存に一般化してはいけない。

## 証明した不等式

語が AAS で始まれば長さ3の prefix がすでに P2。よって最小 lag>3 の窓は先頭 A run が 2 ではない
（0、1、または ≥3）。a≥3 でその直後が S なら、同じ履歴の `t-(a-2)` は現在 A で、長さ3の過去が AAS。
標準 114 は a=3、兄弟は 113。Lean：`Recaman/TwoSSLeadingSibling.lean`。

これは容量の単射ではない。companion の SS=2 は、すでに low-SS を持つ run の**追加**源である。
newest-S が共同で使えない理由そのもの。

## 有限診断（証明ではない）

標準 10^7、exact prefix-key、lag 上限なし。

| 対象 | 件数 |
|---:|---:|
| 有限 P2 供給 A | 1,315,896 |
| そのうち最小窓 SS=2 | 52,357 |
| companion a≥3（兄弟 AAS 148/148） | 148 |
| 孤立 a=0（直前が S） | 52,198 |
| 孤立 a=1 | 11 |
| a=2 | 0 |
| 同一 A run に SS=2 が2件 | 0 |

SS=2 の 99.7% は孤立 a=0。次の unit はこれらの S 配分。直前時刻 `t-1` は a=0 源のあいだで単射だが、
E-128 との共同は未検査。one-per-run の一般証明も未着手。

再現：

```text
python3 experiments/issue73_20260910/two_ss/classify_and_charge.py
python3 experiments/issue73_20260910/two_ss/newest_s_audit.py
clang++ -O3 -std=c++20 experiments/issue73_20260910/two_ss/orbit_ss2_leading.cpp -o /tmp/recaman-ss2-leading
/tmp/recaman-ss2-leading
```

出力：`docs/data/issue73_20260910/two_ss/`。

## 次の判断

孤立 a=0 に対する、E-128 と交わらない明示的な S 割り当てか、one-per-run の Lean 証明。
oldest-S / newest-S / first-SS の修理、型表、SS≤2 prefix 正規化は再開しない。
E-067 / E-070 は未解決。
