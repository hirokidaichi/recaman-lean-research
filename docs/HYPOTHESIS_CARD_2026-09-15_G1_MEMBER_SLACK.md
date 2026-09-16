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
  2. s が paired older S なら、w の最古 S が s で、その一つ新しい offset も S、すなわち **w の窓は「…S S A^j」（j ≥ 0、最古 S の後ろは A のみ）で終わる**。
     lag 3 は不可、lag 7 なら w1（本カードの補題、j = 0）、lag 11 なら 17 語中 9 語（j = 0：ASASASAAASS, ASSAAASAASS, SAAASSAAASS, SAASAASAASS, SASAAAASASS, SSAAAAAASSS；
     j = 1：ASASAAASSSA (d3), SAAASAASSSA (d6)；j = 2：AAASSASSSAA）。d1/d2/d4/d5/d7 の最古 S は対の古い方ではない。
  3. lag ≥ 11 の v の窓の S の半分以上は対に属す（lag-11 の 17 語中 15 語が paired older S を持つ）。各 paired older S の所有者 w は「…S S A^j」型で、
     w の窓の s より新しい部分（offset 1 から lag(w)−2 まで）が v の窓の bit と整合しなければならない——ここが 17 語 × offset の有限検査。
- 本カードは T・OS のどちらも証明しない。paired older S 補題は「所有者は …SS 型」を言うだけで、所有者が存在すること（OS）は仮定である。

## Decision

- E-352 を `COMPUTED` で登録し、補題を `Recaman/PairedSubtractionCoverage.lean`（E-353）として Lean 化する（E-348 の `coverOK` 型の decide＋stream lift）。
- P2 の紙上証明は E-349 の骨組み（補題 A〜D）を正本とし、本カードの鎖 1〜3 を「T の導出」の具体化として提供する。
- 次の probe：OS を仮定せずに「paired older S を含む窓のメンバーは、その S を最古 S に持つ …SS 型メンバーを B 内に伴う」を緊密集合で数える
  （E-349 の SIB の一般化）。

## Stop conditions

- Q1 が p ≤ 31 で破れたら G1/T は「lag ≤ 11」に弱める（E-349 と同じ）。
- 鎖 1〜3 の有限検査が 1 unit で書けなければ、T は OS からの帰結として `CONJECTURED` に留め、P3（G2 の lag-7 側）へ進む。

## Addendum（2026-09-15 19:20、E-354）：Q1 の holdout 延長と、OS を仮定した閉包探索

### Q1 holdout（`g1_lag_structure_p27_31.txt`、`g1_lag_structure_all_p25_26.txt`）

| 範囲 | 語数 | lag ≥ 11 メンバー数 | Q1 違反 | 備考 |
|---|---|---|---|---|
| high-SS 語、p = 27..31 | 27,948,247 | 41,675,198 | 0 | 4.5 分。Hall は全語で成立。p = 31 で lag-11 メンバー 4.6M、priv = 0 が 40% |
| 全正符号和語、p = 25..26 | 1,761,794 | 969,573 | 0 | 5.2 秒 |

停止条件の horizon p ≤ 31 まで G1-strong（＝E-349 の T）に例外なし。

### OS-closure 探索（`experiments/issue73_20260915/os_closure_search.py`、bit-level、周期性なし）

E-349 の OS（緊密 B の各 S phase はちょうど 1 人のメンバーの最古 S）を **仮定** し、B の lag 最大メンバー v（lag Lv の最小 P2 語）を clock 0 に置く。
v の窓の各 S（v 自身の最古 S を除く）に「lag ≤ Lv の最小 P2 語 w を、その最古 S がその S に乗るように置く」所有者を要求し、置いた w の S にも所有者を要求する
（閉包）。所有者の窓の bit と既に置いた bit（v 自身は A）が矛盾すれば却下。所有者の候補は lag ≤ Lv の全最小 P2 語（lag 3/7/11/15/19 で 1/2/17/155/1636 語）。
周期性は制約を増やすだけなので、この line model で閉包が存在しなければ周期語でも存在しない（所有者の窓は周期 p だけ平行移動して S に揃えてよい）。

| Lv | v の語数 | 所有者候補 | 全分岐が矛盾で終わる v | 一貫した閉包が見つかる v | cap 到達 | 最大ノード数 | 時間 |
|---|---|---|---|---|---|---|---|
| 11 | 17 | 20 | **17** | 0 | 0 | 25 | 0.02 秒 |
| 15 | 155 | 175 | **155** | 0 | 0 | 168 | 1.3 秒 |
| 19 | 1,636 | 1,811 | **1,636** | 0 | 0 | 2,456 | 8 shard 並列で約 4 分（`os_closure_lagmax19.txt`） |

**モデルの健全性**（`os_closure_lagmax7_sanity.txt`）：同じ探索を lag-max 7 に掛けると w1 = SAAAASS は **{u−3: AAS, u: w1, u+2: AAS} の一貫した閉包**
（E-349 の w1 三つ組そのもの）を返し、w2 = ASAASAS は排除される（E-349 の W2）。lag-max 3 は AAS 単独で閉包。つまりこの探索は実在する緊密モチーフを正しく通し、
lag ≥ 11 だけを落としている。

**lag-max 仮定は不要か**（`os_closure_lag11_owners19.txt`、`os_closure_lag15_owners19.txt`）：所有者候補を lag ≤ 19（1,811 語）まで広げても、lag 11 の 17 語
（最大 873 ノード、74 秒）と lag 15 の 155 語（156 秒）は全て排除される。つまり lag 11／15 のメンバーの排除は「B の他のメンバーがそれより長くない」
という仮定に依らず、v の窓の近傍で局所的に決まる（所有者の lag が 23 以上の場合だけ未検査）。

**帰結**：OS の下では、緊密 B の lag 最大メンバーは lag 11・15・19 のいずれでもあり得ない。すなわち **OS ⇒ T（lag ≤ 19 の範囲で）** が bit-level の有限探索で確認された。
探索木は小さく（lag 11 で ≤ 25 ノード）、`os_closure_lagmax11_trace.txt` に全分岐の却下理由（どの clock で bit が矛盾したか）を残した。
典型的な却下：v の newest 側の A-run（offset 1..3 が A、clock 0 が A）が、paired older S の所有者（…S S A^j 型）の newer 部分の S と衝突する。
lag 11 の 17 語では、最初の 2 個の S の所有者（AAS と w1）を置いた時点で 3 個目の S の所有者が全て矛盾する。

**Lean 化の見通し**：lag 11 の場合は「17 語 × 所有者 20 語 × 配置」の decide で書ける（E-348 の `coverOK` と同型）。ただし前提 OS が未証明なので、
Lean 化しても「OS ∧ lag-max = 11 ⇒ False」という条件付き命題になる。OS 自体（E-349 補題 C/D）が P2 の本体であることは変わらない。


### 一般 lag への帰納のための所有者配置補題（紙上、未 Lean、2026-09-15 19:25）

v（lag L、最古 S を除く S の offset k）の S を x（lag Lx、最古 S の offset kx）が所有するとき、x の加算は clock −k + kx にあり：

1. x の最古 S より古い bit（offset kx+1..Lx）は全て A で、clock −k−1 … −k−(Lx−kx) に乗るので、**v の offset k+1..k+(Lx−kx) は全て A**（v の窓の外に出る分は自由）。
2. x の newer 部分（offset 1..kx−1）は clock −k+1 … −k+kx−1 に乗る。kx ≥ k なら x の offset kx−1..kx−k+1 は v の offset k−1..1 と一致し、
   x の offset kx−k は clock 0（v 自身）なので A、それより新しい offset は v の未来で自由。kx < k なら x の newer 部分全体が v の窓内
   （v の offset k−1..k−kx+1）と一致し、x の加算 clock −k+kx は v の offset k−kx で A でなければならない。
3. x の S は v の S（既に所有者を要求済み）か、v の未来（clock ≥ 1）の新しい S。未来の S の所有者はさらに未来へ延びる窓を要求し、
   その窓の「最古 S より古い A-run」（1.）が v・既置の窓と衝突して連鎖が止まる——探索木が小さい理由。

探索の深さ（`ownedS(v) max` = ある分岐で v の S のうち同時に所有者が置けた最大数、v 自身の最古 S を含む）：
lag 11（S 5 個）：2 個 7 語・3 個 6 語・4 個 3 語・**5 個（全部）1 語**（矛盾は所有者が持ち込む未来の S の連鎖で出る）。
lag 15（S 7 個）：2:40・3:66・4:37・5:9・6:3、7 個は 0。lag 19（S 9 個）：2:174・3:763・4:479・5:166・6:42・7:12、8 個以上は 0。
つまり lag ≥ 15 では v の S 全部に同時に所有者を置くことすらできず、矛盾は v の窓内で閉じる。lag 11 の 1 語（d7 = SAAASSAAASS）だけが未来へ延びる。

帰納の形：lag-max L の v について「v の newest 側から順に S の所有者を置くと、有限段で 1.〜3. が矛盾する」を、v の先頭 A-run の長さ
（E-090：run m0 ≥ 3 ⇒ L ≥ 4m0−1）と所有者の kx の場合分けで書く。探索の `ownedS(v) max` 列（何個の S に同時に所有者が置けたか）が帰納の深さの目安。

### 誠実な注意

- OS は E-349 の COMPUTED 事実であり、証明されていない。本探索は「OS が証明されれば T は lag ≤ 19 で有限検査に落ちる」ことを示すだけで、T の無条件証明ではない。
- lag 23 以上は Python の探索では非現実的（最小語 ≈ 1.7 万、所有者 ≈ 1.9 万）。一般 lag は帰納で扱う。
- 一般 lag への帰納は未着手。lag 4m+3 の v の窓の先頭 A-run（E-090：run m ≥ 3 ⇒ lag ≥ 4m−1）と所有者の newer 部分の衝突を一般に書くのが次の紙上課題。

### 追記（2026-09-16、E-356）

OS の仮定は不要になった。所有者を「最古 S を乗せる」ではなく「任意の S offset を乗せる」として同じ閉包を取ると、Hall の定理のマッチングの片側だけで
lag-max 11／15 と w2 が全排除される（[H-20260916-01](HYPOTHESIS_CARD_2026-09-16_MATCHING_CLOSURE.md)）。本カードの鎖 1〜3 と所有者配置補題は
「任意 offset」版に読み替えて一般 lag の帰納に使う。
