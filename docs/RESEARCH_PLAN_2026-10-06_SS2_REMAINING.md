# 2026-10-06 後半：二窓問題の残余と次の方針

結論：**NoSAAS の下で、二つの SS 辺が一つの SSS run にまとまる衝突対の
局所容量を紙上で証明した（PROVED-PAPER、独立監査 PASS）**。
この条件下の二窓問題では、残るのは二つの SS 辺が別々の run にある場合である。
Lean 化はまだ行っていない。NoSAAS を仮定しない一般問題、複数の衝突対の同時配分、
SS≥3、E-070、E-067、全域性 E-001 は未解決のままである。

基準は 65c25ab742ab4aa749bfd5f48438dbcb7b774d1d。
GPT-6.1-Sol の紙上研究、親の端点反証器、別セッションの監査を並行した。
一次チェックアウトの未統合研究・未コミットファイルは変更していない。

## 「残りが狭まった」の正確な意味

| 対象 | 今回終了時の状態 |
|---|---|
| 任意長 lowSS 集合の端点単射と SS2 最古 S の排除 | 既存 E-368、PROVED-LEAN |
| 同じ最古 S の衝突群は高々二窓 | 既存定理からの紙上帰結 |
| NoSAAS 衝突対の prefix | 純交替形、または (SA)^j A の二形へ限定、PROVED-PAPER |
| NoSAAS・一つの SSS run を持つ衝突対＋任意 lowSS 集合 | **今回 PROVED-PAPER**、全周期・全 lag、正の周期質量も不要 |
| NoSAAS・離れた二つの SS run を持つ衝突対 | CONJECTURED。最小窓と衝突条件を全部満たす実例の有無から確認する |
| NoSAAS なし、複数衝突群、SS≥3、一般容量・全域性 | 未解決。この部分証明からの接続は別の義務 |

従って、今回は単に有限検査の上限を伸ばしたのではなく、無限個の周期・lag を
含む一つの構造的場合を除けた。ただし全域性までの残りを割合で評価できる段階ではない。

NoSAAS は SAAS という符号部分列が現れない条件である。
標準実軌道の有限窓については
CanonicalSSFreeSupply.canonical_noSAAS が既に Lean 証明済み。
任意有限 seed 版や二方向周期語への接続は、使用する際に前提を別途確認する。
ここで NoSAAS を加えたことを、元の無制約な H-01/H-02 の解決と読み替えない。

## 今回の一様な証明

P2 は newest-first 窓の mass=1、moment=0。
二つの current-A 最小 P2 窓は SS=2 で真の最古 S 位相を共有するものとする。
整数時刻を周期移送すると

W_A=C A、W_S=X C

と書け、C は mass0、moment−d_A、SS2。
NoSAAS の下で X は純交替形 (AS)^(d_A−1) A、
または (SA)^j A（j≡2 mod4、j≥6）に限られる。

E_low を「全ての current-A・S-ended・SS≤1・P2 窓の端点位相」の集合とする。
最小窓だけでなく、全ての正の lag を含める。
共通最古 S の時刻 s は E-368 により E_low の外にある。
新しい証明は、そこに追加できる第二の S を実際の符号列から得る。

1. **SSS の年代順最初の S、q は端点になれない。**
   current が q+1 または q+2 なら current 自体が S。
   それより後なら窓に SSS 全体が入り、SS≤1 に反する。
   q>s なら q と s の位相も異なる。同じ位相なら周期性により
   (s,s+1)、(q,q+1)、(q+1,q+2) の三つの SS 辺が C に入り、SS=2 に反する。
   この内部 SSS の補題自体には NoSAAS は不要。

2. **純交替 X では q=s は不可能。**
   仮に C=T SSS とすると、T は SS-free・mass3・末尾 A。
   A run の個数と NoSAAS から二形を尽くせる。
   start-A 型は T=(AS)^a AAA(SA)^b で moment 条件 a=3b+2。
   C の先頭 AS と実 current A と X の末尾 SA が SAAS を作って矛盾する。
   start-S 型の A⁴ run は 3j−3b−2=0 を要求し、mod3 で不可能。

3. **もう一方の X で q=s なら、次に古い S、s+1 を使う。**
   同じ分類から C=(AS)^a AAA(SA)^b SSS、a=3b+2 を得る。
   s=0 に正規化すると、端点1から A-ended current t_A までの年代順符号は
   SS(AS)^b AAA(SA)^a。mass1 の current-A 候補は t_A のみだが、
   その窓は lag d_A−2、moment−1 なので P2 でない。
   次の X.reverse=A(AS)^j の部分では mass は2/3。
   さらに未来へ伸ばしても、端点付近ですでに SS 辺を一つ使っているため、
   低SS窓の追加部分は A 始まりの SS-free 語であり、追加 mass≥0。
   全ての未来時計で mass≥2 のため、端点1の P2 は存在しない。
   位相(s) と位相(s+1) は異なる（p=1 では S と current-A が共存できない）。

これで SSS 型の全場合について |N_pair \ E_low|≥2。
任意の lowSS 集合 L の実際の窓内にある E-368 の単射端点像 F⊆E_low と合わせると

|N(L ∪ {v,w})| ≥ |L|+2

が従う。Hall、owner、未証明の「第二 S 仮説」は仮定していない。
[完全紙上証明](data/ss2_pair_endpoints_20261006/sol61/report.md)、
[独立再構成](data/ss2_pair_endpoints_20261006/audit/capacity-subcase-addendum.md)、
[最終枝の監査](data/ss2_pair_endpoints_20261006/audit/oldest-sss-endpoint-addendum.md)
を参照。

## 反証・計算とその限界

- 新しい強い候補 |N_pair \ E_low|≥2 は、前回と同じ周期1〜22を再使用して検査。
  24組の全端点集合を独立再計算し、違反0、最小除外数5（COMPUTED）。
  元の容量不等式より強い候補であり、将来この候補が破れても元の不等式の反例とは限らない。
- NoSAAS 衝突も周期22に **1件ある**。周期33は最小例という主張ではない。
  第一の prefix 形は周期33、第二形は周期22の具体例で確認した。
- 「NoSAAS なら最古 S の衝突がなくなる」は REFUTED。
  固定 V=(AS)^10 A AAASSSASAS に対し、周期語 reverse(V) A^n、n≥2 は
  全ての周期パラメータ p=31+n≥33 で正質量・NoSAAS の衝突を作る。
  これらは今回の SSS 容量証明で扱える。衝突の存在と容量不足は別の主張。
- 新補題の固定 controls は discovery4例、holdout2例。
  NoSAAS を外すと純交替型でも q=s となる境界例を保存した。
  途中で現れた一パラメータ形
  C=(AS)^(9r+5) AAA(SA)^(3r+1) SSS、X=(SA)^(8r+6) A
  は r=0,1,2 の exact controls を通した。
  この形の全未来端点排除は上の紙上議論で証明する。三例の計算を一般証明には使わない。
- 最終的な s+1 排除の着想は controls の後に得た。既存出力の再利用であり、
  この最後の着想に独立の未使用 holdout があるとは主張しない。
  一様な結論の証拠は、独立監査を受けた全時計の紙上議論である。

[H-02カード](HYPOTHESIS_CARD_2026-10-06_SS2_PAIR_ENDPOINTS.md)、
[H-03カード](HYPOTHESIS_CARD_2026-10-06_SS2_INTERNAL_SSS.md)、
[端点検査の exact output](data/ss2_pair_endpoints_20261006/holdout.jsonl)、
[controls](data/ss2_internal_sss_20261006/discovery.json)、
[holdout controls](data/ss2_internal_sss_20261006/holdout.json)に再現記録を残す。

## 次の方針と停止条件

次の研究上の一問は、**NoSAAS の最小 A-ended SS2 窓で、二つの SS 辺が
別々の run にある場合が、同じ最古 S の衝突対として実現できるか**。
今回の SSS 端点禁止則は、そのまま SS 二組には適用できない。

- 最初に全前提を満たす具体的な実符号列・周期語を作るか、存在不能を一様に証明する。
  単なる SS2 語だけ、最小性なし、current-A なしの例は受理しない。
- 実例があるなら、その二つの SS run の端点が低SS窓に使われる条件を
  一つの falsifiable な不等式にする。固定した S の名前を次々変える方法には戻らない。
- 例が見つからないだけでは枝を削除しない。30〜60分で構造的補題も反例も得られなければ、
  この探索は STOPPED として保存する。周期上限だけを増やし続けない。
- 実装上の次の単位は今回の SSS 容量証明の Lean 化。
  最初の SSS 端点禁止、位相分離、q=s の二場合を含む正確な statement を一つの
  モジュールで扱い、反証 controls・独立 statement audit・全体 check を通す。
  補助構造だけを形式化して容量証明完了としない。

単一衝突対を解いた後も、複数対の第二 S が互いに重なる問題と SS≥3 が残る。
その後に E-070/E-067 との接続を検討する。非周期性から全域性は直ちには従わない。
今回の進捗を全域性の証明と表現しない。

## 変更・検証の引き継ぎ

変更は研究カード、証拠台帳・proof map・frontier、実験コードと監査/出力、
この方針記録。Lean と保護された中心主張は変更しない。
C++の固定範囲検査、Python直接再生、別実装の全端点集合比較、
六つの構成例の独立再生、紙上の全場合監査を実施した。
コマンドと source hash は各 data directory の README / audit / SHA256SUMS に保存する。

