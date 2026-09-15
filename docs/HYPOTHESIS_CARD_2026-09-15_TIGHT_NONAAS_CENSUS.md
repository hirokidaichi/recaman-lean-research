# Hypothesis card: tight avoiding subsets with a non-AAS member, and which subtraction a high-SS window can donate

- ID: `H-20260915-18`
- Created: 2026-09-15 16:20 JST
- Status: `COMPUTED`（E-345）。E-070 / E-067 / Gate T6（一般 p）は `CONJECTURED` のまま
- Research branch: issue #73、E-343 監査（geometric/pure-AAS 路線 STOPPED）の直後
- Probe: `experiments/issue73_20260915/tight_nonaas_census.cpp`（8 ≤ p ≤ 22、0.4 秒）、
  独立検証 `experiments/issue73_20260915/verify_witnesses.py`（共有コードなしの直接和）
- Output: `docs/data/issue73_20260915/tight_nonaas_census.txt`

## Exact statement

E-179 と同じ設定。周期 p の正符号和語、`U` = 最小 P2 窓を持つ加算 phase、`lag(t)` = 最小 lag、
`N([t])` = 窓内の減算 phase、`N(B) = ∪_{t∈B} N([t])`。donor `u0` は最小窓の `ssCount ≥ 2` の供給 phase、
`s*(u0)` = donor 窓の最古の減算 phase（Lean の `oldestSubtractionPhase`）。
`B ⊆ U ∖ {u0}` が **緊密回避** とは `|N(B)| = |B|`。lag 3 の P2 窓は AAS そのものなので、
**非 AAS** とは「lag ≠ 3 のメンバーを含む」こと。

凍結した問い（走らせる前に決めた）:

```text
Q1  非 AAS 緊密回避部分集合が初めて現れる周期 p は？ ss=2 donor に限ると？
Q2  p = 19..22 で、非 AAS 緊密回避部分集合を持つ donor の割合は？（1% 未満なら「稀な例外」として
    純 AAS 路線の case split を再開してよい。以上なら路線は STOPPED のまま）
Q3  s*(u0) ∈ N(B) となる緊密回避 B（＝最古 S の削除で Hall が破れる）は存在するか？
    donor を ssCount=2 / ssCount≥2 で分けて数える。E-179（何らかの S は削除可能）と照合する
Q4  緊密回避部分集合に現れる lag の集合は？
```

受入条件: `wordsWithHighSS` が全 p で E-179（`local_surplus.txt`）と一致すること（不一致なら abort）。
部分集合列挙による「s* が被覆される」と matching による「s* を禁じると Hall が破れる」が全 donor で一致すること
（不一致なら exit 2）。証人 2 件は独立実装で再計算する。

## Results（p = 8..22、necklace 代表、E-179 と全周期で一致）

| p | high-SS donors | 緊密回避を持つ | 非AAS緊密回避を持つ（全donor） | 同（ss=2 donor） | ss=2 donor 数 | 最古S削除不可（ss=2） | 最古S削除不可（ss≥3） | 緊密内の最大 lag |
|---|---|---|---|---|---|---|---|---|
| 8..11 | 1,3,1,20 | 1,2,1,18 | 0 | 0 | 1,2,1,8 | 0 | 0 | 3 |
| 12 | 19 | 18 | 1 | 0 | 11 | 0 | **1** | 7 |
| 13 | 83 | 75 | 0 | 0 | 27 | 0 | 4 | 3 |
| 14 | 74 | 72 | 4 | 0 | 35 | 0 | 4 | 7 |
| 15 | 358 | 329 | 4 | **1** | 81 | 0 | 8 | 7 |
| 16 | 404 | 391 | 9 | 1 | 149 | 0 | 18 | 7 |
| 17 | 1420 | 1335 | 17 | 2 | 319 | 0 | 73 | 7 |
| 18 | 1591 | 1552 | 40 | 6 | 525 | 0 | 86 | 7 |
| 19 | 5821 | 5533 | 98 | 13 | 1112 | 0 | 202 | 7 |
| 20 | 7082 | 6920 | 173 | 24 | 1972 | 0 | 340 | 7 |
| 21 | 23027 | 22193 | 453 | 53 | 4430 | 0 | 1391 | 7 |
| 22 | 28162 | 27685 | 776 | 114 | 7434 | 0 | 1598 | 7 |

「何らかの S が削除可能」は全 p・全 donor で成立（E-179 の再現）。非 AAS メンバーの lag は全件 **7**（lag ≥ 11 の窓は
p ≤ 22 の緊密回避部分集合に一度も現れない）。非 AAS 緊密部分集合の最大サイズは 3（p=12）→ 6（p=22）。

証人（独立検証済み）:
- p=12 `AAAASAAASSSS`、donor 3（lag 11、ssCount 3）、s*=4、B={2(lag3), 5(lag7), 7(lag3)}、N(B)={4,10,11} 緊密、**s* ∈ N(B)**。
  最古 S の供出はここで初めて破れる（ssCount 3）。
- p=15 `AAAASAAASASASSS`、donor 3（lag 11、ssCount 2）、s*=8：ss=2 donor で初めて非 AAS 緊密回避部分集合が現れる。
- p=18 `AAAASSAAAASAAASASS`（E-240）、donor 7、s*=14、B={2,8,11(lag7),13}、N(B)={4,5,10,17}、s* ∉ N(B)。

## Answers and decision

- **Q1**: 全 donor では p=12（ssCount 3 donor）。**ss=2 donor では p=15**。従って「緊密回避 ⇒ 純 AAS」は ss=2 donor に限れば
  p ≤ 14 で真、p ≥ 15 で偽（E-240 の p=18 は最初ではない）。
- **Q2**: p=22 で 776/28162 = 2.8%（全 donor）、114/7434 = 1.5%（ss=2 donor）。1% を超え、しかも p とともに増える。
  **純 AAS 路線（E-297〜E-317 の目標命題）は STOPPED のまま。** 例外は「lag 7 メンバーを含む」だけで構造は単純。
- **Q3**: **ssCount = 2 donor の最古 S は p ≤ 22 で一度も緊密回避部分集合に被覆されない**（donor の lag を問わず）。
  これが Lean の Gate T6（`hss0 : ssCount = 2`、`oldestSubtractionPhase`）の一般 p 予想の正しい形であり、p ≤ 10 の
  E-230/E-231 と整合する。一方 **ssCount ≥ 3 の donor では最古 S の供出は p=12 から破れる**（p=22 で 1598/20728）。
  E-179 の「何らかの S」は常に存在するので、一般 T6 は ssCount ≥ 3 で供出則を変える必要がある（最古 S ではない）。
- **Q4**: 緊密回避部分集合の lag は p ≤ 22 で常に {3, 7}。ループが常設仮定にしていた `hU_lags : lag ∈ {3,7}` は
  緊密回避部分集合のメンバーについては経験的に正しい（U 全体についてではない）。

## Next gate（E-343 の再開条件をこの結果で具体化する）

Lean 目標は次の 2 命題に絞る。どちらも実際の符号語 `e` と周期 `p` を binder に持ち、p の上限を置かない。

```text
G1 (lag set)   tight avoiding B（ss=2 donor を避ける）のメンバーの最小 lag は 3 か 7
G2 (oldest S)  ss=2 donor の最古 S は、lag ∈ {3,7} のメンバーからなる緊密回避 B に被覆されない
```

G2 は p ≤ 14 なら「全員 lag 3」から従う（既存の AAS 回避補題）。p ≥ 15 では lag 7 メンバーが実在するので、
lag 7 窓の S 集合（offset {1,6,7} または {2,5,7}、E-305 の w1/w2）と ss=2 donor の最古 S の位置関係を直接扱う補題が要る。
E-311（lag 7 窓同士の距離 ≥ 5）と E-267（`s ∈ N(B) ↔ ∃ u ∈ B, s ∈ N([u])`）はこの形で再利用できる。

## Stop conditions

- G1 または G2 の反例が p ≤ 31 の網羅で出たら、Gate T6 の一般形は最古 S 以外の供出則へ移る（E-179 の「何らかの S」）。
- 周期の horizon 延長だけでは label を上げない（同期規則 3）。
