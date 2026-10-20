# Hypothesis card: line capacity (Conjecture H) and its equality cases

- ID: `H-20261020-01`
- Owner: Claude Opus 5.5 session（2026-10-20 夜、広木さん指示「5時間ほど研究をすすめて」）
- Created: 2026-10-20 20:15 JST
- Status: `CONJECTURED`
- Research branch: issue #73、研究計画 P2（G1）。[H-20261003-01](HYPOTHESIS_CARD_2026-10-03_GENERAL_LAG_CLOSURE.md) の Claim P の続き。

## Exact statement

符号語 σ : ℤ → {A = +1, S = −1}、F(t) = Σ_{c<t} σ(c)。clock b の P2 窓とは [t, b−1]（長さ L = b − t ≥ 1）で
Σ_{c∈[t,b−1]} σ(c) = 1 かつ Σ_{c∈[t,b−1]} σ(c)(b − c) = 0（最小性は課さない）。b が **p から終点可能**とは σ(b) = A かつ t ≥ p の P2 窓 [t, b−1] があること。

```text
H（区間容量）
  任意の σ と任意の p < k について
    e_p(k) := #{b ∈ [p, k−1] : b は p から終点可能}  ≤  s_p(k) := #{c ∈ [p, k−1] : σ(c) = S}.

EqClass（等号の場合）
  σ(·) と p < k について e_p(k) = s_p(k) かつ k−1 が p から終点可能なら、
  σ[p, k−1] は (SAAA | SSAAAASAAA | A)* と（一意に）分解し、p から終点可能な clock はちょうどブロックのメンバー
  （SAAA の 4 文字目、SSAAAASAAA の 5・8・10 文字目）で、各々の P2 窓（始点 ≥ p）は長さ 3 / 7 のブロックの窓 1 本だけ。
```

Lean 上の述語（E-370）：`LineCapacity e := ∀ q n, endableCount e q n ≤ subtractionCount e q n`
（`Endable e q b := e b = true ∧ ∃ d, 0 < d ∧ q ≤ b − d ∧ P2 (past e b d)`）。

## Why it would matter

- **H ⇒ E-070**（周期語の |U| ≤ |D|）。証明：区間を周期の K 倍に取り K → ∞（E-370 で Lean 化、`periodic_capacity_of_line`）。
  つまり H は中心予想 E-070 の有限・非周期な強化で、H の証明は E-070・E-067 の証明になる。
- **H ⇒ Hall**：P2 窓の任意の族（終点相異）の部分族の和集合を成分に分けると、各成分の窓は区間の終点可能な clock に数えられるので
  #S(和集合) ≥ #窓。従って閉包（M1・単射・M2）とは「#窓 = #S(和集合)」の族であり、成分は H の等号の場合、成分内の終点可能な A は
  全てメンバー（飽和）。**EqClass ⇒ 閉包の分類 ⇒ Claim P ⇒ G1（全 lag）**（E-367 `motifFull_of_private`）。
- 2D の言い換え：P(z) = (F(z), Σ_{c<z} σ(c)c) は ±(1, z) で動く。b が終点可能 ⇔ P(b) − (1, b) = P(t)（p ≤ t < b）、
  すなわち「b で引き算すると区間内で既に訪れた点に戻る」。Recamán の規則を符号和の座標付きで述べた形。

## Provenance and dependencies

- 発見：サブエージェント levels（2026-10-20、Claim P の水準方向の探索中）。親が「E-070 の line 版」であることと周期版への帰着を指摘・Lean 化。
- 依存：E-362（P2 の水準恒等式）、E-364〜E-367（閉包の枠組み）、E-071/E-080/E-128（E-070 の特殊例の Lean 証明）。

## Falsification plan / Evidence log

| 主張 | 検査 | 結果 |
|---|---|---|
| H | `experiments/issue73_20261020/hall.c`（`./hall 34`、全 p は部分語として網羅） | 長さ ≤ 34 の全 2^34 語で max(e − s) = 0（`docs/data/issue73_20261020/hall34.out`） |
| H（独立実装） | `eqcheck.c`（親、`./eqcheck 24`） | 長さ ≤ 24 で違反 0 |
| EqClass（分解） | `eqparse_any.c`（任意の始点、`./eqparse_any 30`） | 13,373 例、分解失敗 0 |
| EqClass（窓の一意性） | `eqwin_any.c 32` | 26,443 例、2 本目の窓 0、長さ > 7 の窓 0（`eqwin32.out`） |
| EqClass・H（独立実装） | `eqcheck.c 31`（親、20:19 完了） | 長さ ≤ 31 で H 違反 0、等号の場合 18,806 例で分解失敗 0 |
| 水準ごとの H | `hl.c` | **偽**：SSSSSSSSSAAASSSSAAAASA（水準 −8 で終点 3、S 2） |
| 1 次元版（Σσc の条件のみ） | `h1d.c 22 0` | **偽**：長さ 17 で e − s = 4（mass 条件が本質） |
| 窓内の正準単射 | levels の inj*.c | 最古 S（S^11 AAA SSSS AAAA）、最新 S（S^14 ASAASAAA）、基底水準の最新 S（S^12 AASAAASSAA）などすべて衝突 |
| moment の片側緩和 | `lv.py --moment le/ge --P` | どちらでも Claim P が偽（ge 側：AASASSAAASSSSA、メンバー 3:[0,2]、7:[0,6]、8:[1,7]） |

**計算機援用の有限定理（E-369）**：H（長さ ≤ 34）と EqClass（長さ ≤ 30）と上の飽和論法から、各成分の幅（最新メンバーまで）が 30 以下の
有限閉包は孤立 AAS と w1 三つ組の和。窓長・同時に開く窓の数に制限はない。

## 同日の Claim P への直接攻撃（紙上、親が要点を検算）

1. **E と D は所有写像に依らない**：E(z) = #{始点 < z} − #S[x, z)、D(z) = #S[x, z) − #{メンバー ≤ z}。SC ⇔ E ≡ 0 ⇔
   「窓の始点が相異なる S clock」。SC の下で所有写像は一意（b ↦ t_b）。
2. **最初の破れは最古の始点 x で起きる**（SC の極小反例、E 分割による）。
3. **最小反例の核と尾**：z* = min{z > x : E(z) = 0} 以降は孤立 AAS・三つ組・自由な A の列（尾）、[x, z*) が核。尾の判定は窓長に依らず有限
   （ブロック境界で G が +1/+2/+4 上がり、G ≥ 4 なら閉じられない）。**核の S が 5 個以下の最小反例はない**（lag 一様の有限探索、
   `experiments/issue73_20261020/core_oldest/core.py 5 eq`、1,050 万ノード）。monovariant 側の独立な探索（`core_monovariant/coretail.py`）は
   長さ ≤ 16 の核（同時 ≤ 4 窓・同時刻始点 ≤ 2）で 0。
4. **否定的結果**：窓ごとに足し合わせる単調量（Φ = Σ f(窓の型) + g(E)）は存在しない（LP 非実行可能、lag 一様の証明書：x で 2 窓が始まり
   x と x+1 を所有する状態は w1 接頭辞 2 個の和に見えるが死んでいる）。「最古の保留窓は閉じない」は偽（ASSASAA の lag-7 窓が閉じる）。
   moment を自由にした一般化閉包での「破れ ≤ ½Σ|moment|」は幅 18 で偽（ASSASAAAASASAASAAA）。

## Clean Window 定理（サブエージェント hinduct の紙上証明、親が検算）

endable b の最小窓 [t, b−1]（最も遅い始点）、h = F(t)、P_h(u) = Σ_{w≤u} F(w) − h·u（P_h(u') − P_h(u) = Σ_{w=u+1}^{u'} (F(w) − h)）。
(t, b) が P2 ⇔ F(t) = h、F(b) = h + 1、σ(b) = A、P_h(t) = P_h(b) =: v。**b が clean** ⇔ 窓の内側で基底水準に戻る全ての u（t < u < b、F(u) = h）で P_h(u) < v。

- (A) clean ⇒ σ(t) = S（σ(t) = A なら最初の戻り u で P_h(u) > v、戻りがなければ P_h(b) > v）。
- (B) (t, b) が P2 で b < b' が同じ始点 t の P2 窓を持てば b' は clean でない（b の後の最初の h 訪問 ρ で P_h(ρ) > v、なければ P_h(b') > v）。
- **定理**：b ↦ t*_b は clean な endable 上で単射で、像は区間内の S。従って **endable が全て clean な区間では H が成り立つ**。
  clean は ssCount ≤ 1 の窓（E-128 の拡張）と深さ 1（窓内で h − 1 より下に行かない）の窓を全て含む。
- unclean な窓は深さ ≥ 2 の下向き遠足で v を飛び越える（その前に上向きの飛び越えか A 始まり）。
- **H+**：e_p(k) + u_p(k) ≤ s_p(k)（u は unclean な endable の数）。長さ ≤ 32 で例外 0（hinduct の p8.c）だが、**親の `hplus.c` の長さ 35 走査で
  長さ 34 の反例**：SAAASSSSAAAASASSSAAASAAASSAAAASAAA（e = 11、u = 3（b = 11, 22, 26）、s = 13、H 自体は成立）。unclean を一律に 2 個分と数える課金は不可能。
- **否定的結果**：clean → t* を固定した単射は unclean に延長できない（長さ 28：SAAASSSSAAAASASAASASAAAASSSA、unclean b = 11 の窓 [0,10] の S 0,4,5,6,7 が
  clean な 3、27、20、13、10 の t* で埋まる。b = 27 を 24〜26 へ移せば解消）。unclean b の行き先を窓内の局所規則（飛び越え遠足の始点・最新 S・
  最後の上向き遠足など）で決める案は全て衝突。

## Decision

- H と EqClass を次の目標とする。H は E-070 を含意するので、ここが問題の核心。
- Lean：E-370（H ⇒ 周期版容量）。次は「H ∧ EqClass ⇒ 閉包の分類」の Lean 化、または H の部分クラス（lag ≤ 7 の line 版など）。
