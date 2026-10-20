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

## 窓長制限・水準・深さ 2（2026-10-20 夜、第 2〜3 ラウンド）

- **H_L（窓長 ≤ L）は L ≤ 31 で全語成立**（E-372、有限状態グラフの最大累積 0。親 `bounded_lag_capacity.c` とサブエージェント hpot `potL2.c` が一致、
  緩和した moment では違反を検出）。周期語へ持ち上げると lag ≤ 31 の供給の E-070。
- hpot：(d, c) 状態（c = 面積 − d(d+1)/2、A で (d+1, c)、S で (d−1, c+2d−1)、終点 ⇔ A で (1, −1) あり）。水準ごとの H は深さ ≤ 1 か高さ ≤ 1 の窓で全 lag で成立
  （紙上、定理 A/B/U）、深さ 2・高さ 2 で偽。開始点の和に分解するポテンシャルは LP で不可能。
- hunclean：補題 0（パリティ：基底水準の訪問 u で P_h(u) = P_h(b) なら [u, b−1] は P2）、補題 1（r_b ＝ 面積 ≥ v の最後の基底水準訪問は S。
  r_b = t* ⇔ clean。r は単射でない）。U1・U3（水準付きの照合）が長さ ≤ 34 で成立。
- htrunc（親が補題 B・Q を検算）：補題 A（基底より 2 以上下の遠足は半長 n と面積 Q が同じ遠足に置き換えても無関係）、
  **補題 B**（unclean b で r = 面積 > 0 の最後の基底水準訪問とすると r と r+1 は共に S）、**補題 Q**（r より前で高さ h+1 の最後の S q は t* < q < r で、
  q から始まる P2 窓は全て深さ ≥ 3）。**DF2**（深さ ≤ 2 の unclean は自分の窓内の「深く落ちる」高さ ≥ h+1 の S へ単射に送れる：長さ ≤ 31）と Clean Window
  定理から深さ ≤ 2 の H が従う（D2-local は長さ ≤ 34 で直接確認）。**ただし DF2 は長さ 32 で偽**（サブエージェント df2：ASASASASASASSAAASSSSASASAAAASASA、深さ ≤ 2 の unclean b = 27, 29, 31 が同じ r = 18、q = 17 を持ち、深く落ちる S は 16・17 の 2 個だけ。H 自体は成立）。U1-R2（深さ ≤ 2 の clean は t* 固定、深さ ≥ 3 の clean だけが動く）が長さ ≤ 31。
  unclean の行き先を局所規則で決める案は全て非単射（貪欲・完全照合のみ成功）。

## 深さ ≤ 2 の場合（サブエージェント df2、紙上・親が要点を検算）

- 深さ ≤ 2 の下向き遠足は S(SA)^j A（面積 −(1+3j)）。補題 B・Q の深さ 2 版。
- **定理 D**：深さ ≤ 2 の endable で、unclean のものの q_b が相異なる区間では、b ↦（clean なら t*、unclean なら q_b）が単射で H が成り立つ
  （clean 同士は E-371、clean と unclean は補題 Q、unclean 同士は仮定）。SAAASSSSAAA と三つ組を含む。
- **補題 G**（同じ q を持つ unclean の群）：R ＝ q+1 以後で最初に A が続く基底水準訪問、α(t) = 面積 (t, q+1]、β(x) = 面積 (q+1, x]、K = −β(R) とすると
  各メンバーは r_b < R < b、0 < α(t*_b) < K、メンバー b < b' で β(b') ≥ β(b) + 3（始点は相異なり α は 3 以上離れる）。
- **単射 Φ′**（予想）：clean → t*、unclean は q 群ごとに q の昇順・群内は始点の遅い順に「[t*, q] 内で高さ ≥ h+1、深さ ≤ 2 の clean の始点でない、未使用の最新の S」を取る。
  長さ ≤ 30 の全語と長さ 110 程度までのランダム検査 87,000 件で失敗 0（非貪欲版 Φ は長さ 62 で失敗）。H-start（区間内の深さ ≤ 2 の unclean ＋ clean の始点 ≤ S）は長さ ≤ 31。

## H は EqClass に帰着する（サブエージェント pump の紙上証明、親が検算）

- **密度補題**：B*A*（B = {SAAA, SSAAAASAAA, A}）の語の任意の接尾辞 v は 10·#S(v) ≤ 3|v|。P2 窓は 2·#S = |v| − 1 なので、そのような接尾辞は P2 窓でない。
- **定理 1**：長さ n の H は、長さ n 未満の H と EqClassW（等号の場合の分解だけ、窓の一意性なし）から従う（同じ始点 p で）。
  証明：長さ n で破れると [p, p+n−1) は等号で最後の clock は endable。直前の endable までの接頭辞は EqClassW でブロック語、その後は A だけ。
  最後の clock の窓は B*A* の接尾辞になり密度補題に反する。**従って H 全体は EqClassW の帰納段に帰着する。**
- 定理 2・3（最小反例の構造）：最後の 2 つの endable の間は A だけ、x = w·A^i·y（w はブロック語、y は d の最後の零点から S で始まり内部で d > 0）、
  w の各ブロック境界は y で終わる窓にまたがれる。
- DL4（予想、長さ ≤ 30）：長さ ≥ 4 の任意の語に e − s を減らさない連続 4 文字の削除がある（DL4 ⇒ H）。正準的な削除規則は全て失敗。

## 深さ ≤ 2 の H の帰着（サブエージェント qgroup、紙上・親は要点を確認）

- Φ′ は偽（長さ 56：SASASASASASASASASASASASAAAAASSSSSASSASASASASAAAASASASASA、q 群の 5 メンバーに対し [x, q] の供給は 4）。H 自体は成立。
- 中間領域 M_q = [q+1, R)（歩みは [h−2, h]、N 個の遠足 S(SA)^{j_i}A、K = N + 3J）。**補題 I**：異なる q 群の中間領域は互いに素。
- **定理 Σ**：各 q 群で (II)「M_q の、深さ ≤ 2 の clean の始点でない S の数 ≥ m − 1」が成り立てば、clean → t*、群の 1 人 → q、残り → M_q の空き S が単射で、
  **深さ ≤ 2 の endable について H が成り立つ**。(II) は c_1（M_q の高さ h−1 にある clean の始点の数）≤ 1 なら証明済み（値ブロックの数え上げ）、
  一般には長さ ≤ 28 の全語と長さ 220 までのランダム 165 万語で成立。強化版 (II*) は長さ 200 のランダム例で偽。

## EqClassW の帰納段の整理（サブエージェント eqstep、紙上。補題 BW・C の有限検査部分は長さ ≤ 30 の計算、手での上界は要再確認）

- Φ(q) := #{endable b で最小窓の始点 τ_b < q} − #S[p, q) = slack(q,k) − slack(p,k)。等号の語では Φ ≥ 0（接尾区間の H）。
- **定理 R**：等号で最後が endable の語について、ブロック語 ⇔ Φ ≡ 0 ⇔ 全ての接尾区間が等号 ⇔ τ が endable から S への全単射。
- **定理 CC**：最小反例は unclean な endable を持つ（全て clean なら Clean Window 定理で Φ ≤ 0、よって Φ ≡ 0）。
- 二分：(A) τ_{k−1} > p かつ (p, τ_{k−1}] で Φ > 0（このとき始点 p の最小窓を持つ unclean な endable b ≠ k−1 がある）、
  (B) τ_{k−1} = p（語全体が 1 本の最小窓＋終点、長さ ≥ 36）。
- **定理 B（サブエージェント caseB、親が全段を検算）：場合 (B) は起こらない。** x = σ[p, k) が等号で [p, k−2] が k−1 の P2 窓（最小でなくてよい）なら、
  真部分区間の H と短い等号区間の EqClassW（始点 p と p+2 だけ使う）から x = SAAA。証明：等号から終点にならない A はちょうど 2 個で x = S^j AAA…、
  以後の A は全て endable、接頭区間の H で F ≤ 2、F = 2 に達すれば EqClassW で接頭辞が SAAA（j = 1）、最小値の最後の訪問は j、
  水準 −j+1・−j+2 の A は窓の始点がなく F ≥ −j+3、j = 1, 2, 3 は面積・F(L−1) = 0 と矛盾、j ≥ 4 は始点 2 の H で初めて F = 1 になる直前の clock が
  始点 {0, 1} の窓しか持たず、始点 2 からの等号区間が S^{j−2}A で始まるブロック語になって矛盾（j ≥ 5 は SSS、j = 4 は三つ組で F(12) = 2）。
  **従って EqClassW の帰納段（＝H 全体）に残るのは場合 (A) だけ。**
- **場合 (A) の帰着（サブエージェント caseA・caseA2、紙上・親は恒等式を確認）**：c = k−1 の最小窓 [q0, k−2]、y = σ[q0, k)、a_y = y の中の p から endable でない A の数、
  X = y の中で窓が全て q0 より前から始まる endable（はみ出し）の数、d = d(q0) とすると、恒等式 slack(p,k) = d + a_y − 2、slack(q0,k) = a_y + X − 2、Φ(q0) = X − d。
  **定理 A***（a_y + d ≤ 2 なら y = SAAA、定理 B は q0 = p の場合）が場合 (A) を排除し、A* は**はみ出し補題 SL**「a_y + d ≤ 2 なら X ≤ d」から
  定理 B を y に適用して従う。SL は長さ ≤ 28 の全語で成立し、X > d なら a_y ≥ 4 という大きな余裕がある。**H 全体の残りの穴は SL だけ。**
  場合 (A) の形の語は等号を仮定しなくても不足 ≥ 4（長さ ≤ 30）。新しい最古始点の unclean b* は窓長 ≥ 11 で、d(q) = 0 の全ての q より新しい。
  偽：OW（窓の長さ 4m+3 なら不足 ≥ m、長さ 31）、G′（n = 27）。
- **SL の部分的証明（サブエージェント straddle）**：a_y + d ≤ 2 は等号を強制し (a_y, d) ∈ {(2,0), (1,1), (0,2)}。d = 0 では w がブロック語で、
  ブロック接尾辞の正値性（D(t) = F(q0) − F(t) ≥ 1、面積 A1(t) ≥ 1）と「y の走行最小値 + 1 以下の A は endable でない」から y = S^j AAA z、
  **j ≤ 3 なら SL 成立**（j = 1 で y = SAAA、j = 2, 3 は不可能）。未解決：d = 0 で j ≥ 4（q0 をまたぐ早いはみ出し窓 SAAASSSSAAA が現れるが完成しない）、
  d = 1（三つ組の末尾だけが起こる）、d = 2（完成しない）。DFS（|w| ≤ 15・|y| ≤ 80、|w| ≤ 17・|y| ≤ 44）で SL・A* の違反 0。
- **補題 TS（予想、サブエージェント straddle2）**：S だけを挟んで連続する 2 つの endable な A b1 < b2 について、b1 の前の S の連の始点 q* で slack(p, q*) ≥ 3
  （長さ ≤ 30 の全語で成立、最小値 3 は達成：SSAAASSAAASA）。TS ⇒ SL の d = 2 の場合は不可能。証明済み：TS₁（slack ≥ 1）、TS-partial（≥ max(1, 2−j, 3−j−i)、
  j = i = 0 なら TS）、d = 2 で y が AA で始まる場合と F ≤ h2+1 の上限。ブロック語では endable な 2 つの A の間に必ずメンバーでない A がある（補題 M）。
- 深さ ≤ 2 の (II) の残り（c_1 ≥ 2）はサブエージェント qgroup2 が C1 始点の構造補題 L1〜L4 を証明したが未解決。局所的な対応付けは反例で全て否定。
- 予想 PHI：slack(q,k) ≤ 2·slack(p,k)（長さ ≤ 28 の全語で成立、EqClassW を含意）。接尾辞の単調性（slack(q,k) ≤ slack(p,k)）は偽
  （SAAASSSSAAAASAAAAASAAA）。

## EqClass_L の全幅検査（E-374）

H_L のポテンシャル V について、等号語＝空状態から V-タイトな辺だけを通り V = 0 で終わる道（どの接頭辞でも累積 + V = 0）。この道とブロック文法の DFA の積で
EqClass_L を全幅で検査：L ≤ 31 で違反 0（`eqclassL.c`）。周期版はタイトな閉路の因子がブロック語の因子であることを L ≤ 31 で検査（`tightcyc.c`）。
陰性対照と独立監査（`audit/brute.c`・`audit/pbrute.c`）あり。帰結：窓長 ≤ 31 の閉包は全幅で AAS と三つ組の和、lag ≤ 31 の緊密 B の lag は {3, 7}。

## Decision

- H と EqClass を次の目標とする。H は E-070 を含意するので、ここが問題の核心。
- Lean：E-370（H ⇒ 周期版容量）。次は「H ∧ EqClass ⇒ 閉包の分類」の Lean 化、または H の部分クラス（lag ≤ 7 の line 版など）。
