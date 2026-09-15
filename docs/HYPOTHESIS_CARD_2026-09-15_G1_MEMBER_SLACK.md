# Hypothesis card: how far a lag ≥ 11 member is from tightness, and who can cover a paired subtraction

- ID: `H-20260915-21`
- Created: 2026-09-15 18:50 JST（E-349 と同時刻に独立に着手。E-349 の OS 特徴付けを読んだ後に本カードを「補完」として位置づけ直した）
- Status: `COMPUTED`（E-352）。bit-level 補題の Lean 化は E-353（`Recaman/PairedSubtractionCoverage.lean`）
- Research branch: issue #73、研究計画 P2（G1）。[E-349 のカード](HYPOTHESIS_CARD_2026-09-15_TIGHT_OLDEST_S_CHARACTERIZATION.md)の T（lag ≥ 11 は緊密集合に入らない）を
  **メンバー単位**で測り、T の証明に使える局所補題を切り出す
- Probes: `experiments/issue73_20260915/g1_lag_structure.cpp`（E-345/E-349 と同じ列挙、E-179 と語数照合、`--all` で high-SS 窓を持たない語も含める）、
  bit-level 列挙は `docs/data/issue73_20260915/paired_older_s_coverers.txt` 冒頭の Python（周期性なし、lag 3/7/11/15 の最小 P2 語 1/2/17/155 個）
- Output: `docs/data/issue73_20260915/g1_lag_structure.txt`（high-SS 語、p = 8..22、0.5 秒）、`g1_lag_structure_p23_26.txt`（6.5 秒）、
  `g1_lag_structure_all_p8_24.txt`（全正符号和語、1.6 秒）、`paired_older_s_coverers.txt`

## Exact statement

E-345/E-349 と同じ設定。U = 最小 P2 窓を持つ供給 phase、N([v]) = v の窓内の減算 phase、N(B) = ∪ N([v])。
v ∈ U の **private S** とは、U の他のどのメンバーの窓にも入らない N([v]) の元。**minSlack(v)** = min { |N(B)| − |B| : v ∈ B ⊆ U }。
phase s が **paired older S**（隣接 SS 対の古い方）とは e(s) = S かつ e(s+1) = S。

凍結した問い（走らせる前に決めた）:

```text
Q1  G1-strong：lag(v) ≥ 11 の v を含む U の任意の部分集合 B（donor 回避条件なし）について |N(B)| ≥ |B| + 1 か。
    high-SS 窓を持たない語（ss ≤ 1 のみの語）でも成り立つか。
Q2  private S の個数 priv(v) の分布。Hall を B∖{v} に適用すると |N(B)| ≥ |B| − 1 + priv(v) なので priv(v) ≥ 2 なら Q1 は自明。
    priv(v) ≤ 1 の lag ≥ 11 メンバーはどれだけあるか（そこが証明の本体）。
Q3  priv(v) ≤ 1 のメンバーについて minSlack(v) の分布と、minSlack = 1 を達成する B の構成。
Q4  lag-11 窓の各 offset の S が、他のメンバーに「被覆されない／lag-3 だけ／lag-7 を含む／lag ≥ 11 を含む」のどれか。
Q5  bit-level：lag 3/7/11/15 の最小 P2 語のうち、paired older S を含む語と、その offset。
```

受入条件：`wordsWithHighSS` が p ≤ 22 で E-179 と一致（不一致なら abort）。Hall-OK 語内で minSlack < 0 が出たら exit 2。

## Results

### Q1（G1-strong、例外 0）

| 範囲 | 語数 | lag ≥ 11 メンバー数 | Q1 違反（任意 B） | Q1 違反（donor 回避 B） |
|---|---|---|---|---|
| high-SS 語、p = 8..22 | 60,177 | 76,040 | 0 | 0 |
| high-SS 語、p = 23..26（holdout） | 800,841 | 1,099,212 | 0 | 0 |
| **全正符号和語**、p = 8..24（high-SS なし 439,432 語を含む） | 604,846 | 361,556 | 0 | 0 |

全正符号和語で Hall が U 全体で成り立つ（hallOK = 語数、p ≤ 24）。E-349 の T と同じ事実だが、high-SS 窓を持たない語も含めて確認した。
等号語（|U| = |D|、E-176）では U 自身が緊密なので、**等号語には lag ≥ 11 の供給 phase が存在しない**ことになる（E-177 の ssCount ≤ 1 と整合）。

### Q2/Q3（private S と minSlack、p = 22 / p = 26 の lag-11 メンバー）

| p | lag-11 メンバー | priv = 0 | priv = 1 | priv ≥ 2 | priv ≤ 1 のうち minSlack = 1 | = 2 | = 3 | = 4 |
|---|---|---|---|---|---|---|---|---|
| 22 | 7,509 | 2,042 (27%) | 410 | 5,057 | 46 | 878 | 1,290 | 238 |
| 26 | 120,502 | 35,880 (30%) | 6,960 | 77,662 | 770 | 15,430 | 22,475 | 4,165 |

lag 15 では priv ≤ 1 が p=26 で 23,943/88,956、minSlack = 1 は 1 件。lag 19 では minSlack ≥ 2。
**private-S 論法（補題 B 型）は lag-11 メンバーの 3 割で無力**で、minSlack = 1（あと 1 で緊密）の配置が実在する。T の証明は
「v の窓の S を誰が所有するか」（E-349 の OS）を使う大域的な数え上げでなければならない。

minSlack = 1 の最初の証人（全 p で同じ族）：`AAASSAAASAAAAAASSSS`（p=19）、v = 9（lag 11、d7 = SAAASSAAASS 型、ss = 2、priv = 0）、
B = {2(l3), 7(l3), 9(l11), 11(l3)}、N(B) = {3, 4, 8, 17, 18} = N([9])。3 つの AAS が v の非対 S（offset 1, 5, 10）を所有し、
**対の古い方（offset 6 = phase 3、offset 11 = phase 17）は B の誰にも所有されない**。U にはこれらを被覆する lag ≥ 11 の窓があるが（priv = 0）、
それを B に加えると自分の S を持ち込んで slack が増える。lag-11 の ss=3 型（`AAAAAASSAAAASAAASSSSSSSS` v=8、B に w1 を含む）も同じ構造。

### Q4（lag-11 窓の S の offset 別被覆者、p = 22、7,509 窓、private/lag-3のみ/lag-7含む/lag≥11含む）

| offset | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| private | 1047 | 1183 | 932 | 512 | 1048 | 1436 | 1499 | 1970 | 2082 | 2892 | 1983 |
| lag-3 のみ | 596 | 1190 | **0** | 1038 | 1005 | 470 | 477 | 994 | 488 | 511 | 472 |
| lag-7 を含む | 74 | 215 | 104 | 442 | 362 | **0** | **0** | **0** | **0** | 44 | 48 |
| lag ≥ 11 を含む | 847 | 1079 | 409 | 1213 | 1083 | 992 | 1023 | 1204 | 1225 | 1545 | 1811 |

offset 3 の S は 17 語中 `ASSAAAASSAS`/`ASSAAASAASS` だけにあり、常に対 (2,3) の古い方なので lag-3 に被覆されない。offset 6〜9 は lag-7 に一度も被覆されない
（w1 の S は窓の offset 1, 6, 7、w2 は 2, 5, 7 で、lag-11 語との bit 整合が取れない）。offset 10/11 の lag-7 被覆は E-347/E-348 の 3 配置（w1 の newest bit）。

### Q5（bit-level、周期性なし）

| lag | 最小 P2 語 | paired older S を含む語 | 含む offset |
|---|---|---|---|
| 3 | 1（AAS） | 0 | — |
| 7 | 2（w1, w2） | 1（w1 のみ） | 7 のみ（対 (6,7) の古い方） |
| 11 | 17 | 15 | 語ごと（`paired_older_s_coverers.txt`） |
| 15 | 155 | 152 | 同上 |

**補題（bit-level、E-353 で Lean 化）**：paired older S（e(s) = e(s+1) = S）は lag-3 窓（AAS）には入らず、最小 lag-7 窓に入るなら窓は w1 で s は窓の最古 bit（s = u − 7）。
∵ offset k ≥ 2 の S が対の古い方なら offset k−1 も S、offset 1 の新しい隣は加算 u。AAS と w2 には隣接 SS がなく、w1 の隣接 SS は (6,7) のみ。

## What this adds to E-349 and what it does not

- E-349 の T（lag ≥ 11 なし）・W2・SIB は本カードの Q1 と同じ列挙で再現され、さらに high-SS 窓を持たない語でも T が成り立つ。
- 新しいのは Q2〜Q5：T の証明が private-S 論法では閉じないこと（priv = 0 が 3 割）、minSlack = 1 の族の構造、offset 別の被覆者の分類、
  paired older S の被覆者の分類。**E-349 の「T の導出」の有限検査は、次の鎖で書ける見込み**：
  1. OS（E-349、未証明）の下で、緊密 B の各 s ∈ N(B) はあるメンバー w の最古 S。
  2. s が paired older S なら、w の窓は s で終わり（最古 S）、offset lag(w)−1 が S、すなわち **w の窓は「…SS」で終わる**。
     lag 3 は不可、lag 7 なら w1（本カードの補題）、lag 11 なら 17 語中 SS で終わる 6 語（ASASASAAASS, ASSAAASAASS, SAAASSAAASS, SAASAASAASS, SASAAAASASS, SSAAAAAASSS）。
  3. lag ≥ 11 の v の窓の S の半分以上は対に属す（lag-11 の 17 語中 15 語が paired older S を持つ）。各 paired older S の所有者 w は「…SS」型で、
     w の窓は s の直後の A-run と衝突する（v の窓で s の新しい隣は S）——ここが 7 語 × offset の有限検査。
- 本カードは T・OS のどちらも証明しない。paired older S 補題は「所有者は …SS 型」を言うだけで、所有者が存在すること（OS）は仮定である。

## Decision

- E-352 を `COMPUTED` で登録し、補題を `Recaman/PairedSubtractionCoverage.lean`（E-353）として Lean 化する（E-348 の `coverOK` 型の decide＋stream lift）。
- P2 の紙上証明は E-349 の骨組み（補題 A〜D）を正本とし、本カードの鎖 1〜3 を「T の導出」の具体化として提供する。
- 次の probe：OS を仮定せずに「paired older S を含む窓のメンバーは、その S を最古 S に持つ …SS 型メンバーを B 内に伴う」を緊密集合で数える
  （E-349 の SIB の一般化）。

## Stop conditions

- Q1 が p ≤ 31 で破れたら G1/T は「lag ≤ 11」に弱める（E-349 と同じ）。
- 鎖 1〜3 の有限検査が 1 unit で書けなければ、T は OS からの帰結として `CONJECTURED` に留め、P3（G2 の lag-7 側）へ進む。
