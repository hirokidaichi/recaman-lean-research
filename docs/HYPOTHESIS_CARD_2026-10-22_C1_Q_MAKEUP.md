# Hypothesis card: C1 Q の面積分解と最初の障害

- ID: `H-20261022-01`
- Owner: Codex（提案・反証・形式化・監査は別pass）
- Created: 2026-10-22
- Status: `CONJECTURED`
- Work state: 追加cycle終了（10:06:27 JST、実経過98分13秒）。Q全体は未解決
- Parent: [C1](HYPOTHESIS_CARD_2026-10-21_C1_AREA.md)
- Cycle: `R-20261022-MAKEUP`
- 実開始: 2026-10-22 08:28:14 JST、終了期限: 10:08:14 JST（100分）。朝の8時終了を今回には適用しない。

## Exact statement / acceptance

共通記法・完成設定Dは[仮定台帳](RESEARCH_ALLOCATION_2026-10-21.md)。主目標は
全てのDとq0≤b<cについて `F(b)≤g=F(k1) → Z(b)=Σ_(k1,b](F(u)−F(b)+1)≥0`。
受入は全量化子を保つ一様な紙上chain、またはDの全仮定を満たす反例。
有限計算や強い補助命題の反例を主目標の証明・反証と混同しない。

最初のbounded questionは、面積の二項分解の独立な下界がQに足りるか、どの項が破れるか。

```text
Az = Σ_(k1,q0](F(u)−g+1)
Y(b) = Σ_(q0,b](F(u)−F(b)+1)
Z(b) = Az + (q0−k1)(g−F(b)) + Y(b)
```

補助候補A: d≥0 on[p,q0]、d(q0)=1、k1が最後の零点ならAz≥1。
補助候補Y: 上のprefixに、d≥1 on[q0,b+1]、a_p(q0,b+1)≤1を加え、F(b)≤gならY(b)≥0。
これらは完成条件と短いEqClassWを落とす強化版であり、偽でもD版Qは未反証。
この分解自体やQを仮定した帰着は新しい研究成果に数えない。

## Allocation / stopping

- 総枠100分: 開始と反証仕様5、Qの活用60、代替入力の局所探索20、監査・保存15を予定。
- 追加計算は合計CPU上限1200秒（単一worker、終了期限までに終了）、メモリ上限1GiBを初期枠とする。
  紙上検討と計算を同時に行っても延べ研究時間を二重計上しない。
- 補助候補が破れたら反例を保存して主目標へ戻す。一回だけEndableなbへの修理を許す。
  二度目の修理、循環、同じ範囲の無目的な延長で当該方法をSTOPPEDとする。
- 30分時点で反例・新しい独立edgeが得られなければ、最初のZ負化と非Endable Aの関係へ問いを移す。
- 90分からは新探索を止め、意味監査と再現・Leanチェック・引き継ぎを行う。

## Falsification / reproducibility

- discovery: 旧C1実験の小さなprefix範囲を使い、Az/Y/最初のZ負化を新しく観測する。
  既に見た全長≤32の語を未使用holdoutと呼ばない。
- holdout: 独立の長い履歴生成器を凍結してから、一度だけ実行する。範囲・seed・受理母数を実行前に記す。
- 旧 `c1proof/z2.c` は既にAz/Yを調べているため、sourceを確認し、単なる再提案を避ける。
- 全ての計算はrevision、dirty source hash、parameters、正確な出力、CPU/経過時間を保存する。
- 小例: k1=p、b=q0、F(b)=g、S-only尾、終端d(b+1)=0を含む旧probeの広い母集団を区別。
- Lean化は反証passと非循環な紙上chainの後。既存モジュールの純粋なwrapperは作らない。

## Evidence / decision log

| 時刻JST | 役割・作業 | 証拠label / 結果 | 判断・実績 |
|---|---|---|---|
| 08:28:14 | 開始 | CONJECTURED | 100分枠を開始。朝の実績とは別計上 |
| 08:32:47 | 反証・別実装照合 | REFUTED（補助Aのみ） | `SAAA\|SSSSAAAASAAA`, k1=4, q0=16, g=2, Az=−2。a_z=3、F(q0)=4なのでq0自身はQのguard外。Q/Dは未反証 |

### 判定1: 独立なAz下界の方法はSTOPPED

全16clockのF/d/非Endable A数と全始点を独立の直接和で確認した。
Az≥1を単独で証明する案は停止する（旧z2.cにも同じ項の計測があり、新規提案とは数えない）。
Qを修理したのではなく、偽の十分条件を除いた。残る候補Yと、Qの三項が相殺する機構を次の問いにする。
再開条件はAzの追加仮定が完成Dから独立に供給できること。根拠なくAz≥0へ定数を下げて再走しない。

注意: Az≥1は既に最短のz=SでもAz=0のため偽。16clock反例の意味は、定数0まで下げても
独立な非負下界が破れること。最小反例が16clockだと主張しない。

### 次の候補（第2passの後に別判定）

- B: Qのguard下でAz+Y≥0（level補正を使わずに足りるか）。反例なら三項結合が必須。
- R: prefix d(q0)=1でh=F(q0)−g>0なら、Az+h(h+1)/2≥0。
  これはq0からh回のSでgへ初めて下がったときのQであり、一般のyを仮定しない独立の弱い候補。
  h≤0はq0そのもののZを別扱いにする。恒等式を証明しただけでRを証明した扱いにしない。
- 実際のEndableを捨てて個数条件だけ残す弱化historyを攻撃する。
  まずN「走行最小値とその+1のAは非Endable」（既存紙上候補）のみを残した自由tagモデルで反例を探す。
  これは実語のQを反証しない。Nだけで足りなければP2のmomentを使う入力が必要と判定する。

### 判定2: 有限検査（COMPUTED、未証明）

- discovery第2pass: LW28/LY64、1,262,282,377 nodes、362,930,609 guard endpoint。
  Az<0の241,142 endpointでもZの最小1、Yの最小3。Bの全体最小0。
  同じ短語領域の再測定を含み、新しい一様証明とはしない。
- 独立生成holdout: 凍結seed/sourceで80〜384clockの2,000,000語を完了、8群各250,000語。
  B/R/Y/prefix-Q違反0。R最小1、Q最小1、B/Y最小0。
  全始点の直接重み付き和による105入力の実装照合を、holdout generatorを使わず先に実施した。
- holdoutでguardを満たすEndableなbは0だった。これは仮説の空虚な証明ではなく、
  その部分集合では反例候補がなかったという有限結果。完成DのIHは未検査。
- finite horizonの延長だけを続ける方法はここで停止する。次はmomentを残す必要性の診断とRの紙上入力。

### 局所形式化unit: 既存紙上Nの供給（Qの証明とは別）

問い: βがBlockWord、`seg f 0 n=β++A^a`、n≤b、全n≤u≤bでm≤Fw f u、
`Fw f b≤m+1`なら、bは0からEndableでないことを、実際のWin/EndNで示せるか。
量化子は全f,n,a,b,m,β。mは到達した最小値に限らず区間の下界でよい。

依存chain: EndNの窓の始点tを取り、t<nなら既存block_suffix_positive_walkでprefix面積≥1、
窓のmass条件からFw(t)≤m、tailの面積増分≥0でmoment>0。
n≤tならFw(t)=m、全窓が基底以上なので既存dipに反する。
必要な新helperは非負面積増分の延長。Q/R、全区間H/EqClassWは仮定しない。

反証pass: m+1をm+2へ上げるとSAAAのb=3で偽。prefix条件を落とすとSAAAのn=b=3で偽。
尾の下界を落とすとSAAA|SSSSAAAA（b=11）の古い窓が反例となる。
受入は逐語statement監査・全Lean検証。20分で非循環な実装がなければ未検証のまま保存して主Qへ戻す。
この20分は初期の局所探索20分から移し、計算との重複時間を延べ研究へ足さない。
既知紙上Nの形式化を、新しいQの一様下界やC1の解決と呼ばない。

### Nから得た非同値の部分場合: 最低水準をyで訪れるQ（紙上chain、Lean前監査）

同じp基点のEndableを使う。β+A^aのprefix終端をn=k1とし、n≤q0≤r≤b、
Fw(r)=m、全n≤u≤bでm≤Fw(u)、a_p(q0,b)≤1を仮定する。
このときQのguardなしでもZ_n(b)≥0、より強く全n≤u≤bでFw(b)−1≤Fw(u)を主張する。

chain: Fw(b)≥m+2なら、rからbへの離散中間値で、レベルmのA uとレベルm+1のA vを
r≤u<v<bに得る。Nから両方がpから非Endableで、a_p(q0,b)≤1に矛盾。
従ってFw(b)≤m+1。全区間でFw(u)≥mだからZの各項が非負。
Q/R/H/EqClassWそのものは仮定しない。Dからβを供給する前回Pのchainは別依存のまま。

反証pass: ay≤2へ緩めると`SSSAAAS`, n=0,q0=1,r=3,b=6でm=−3、Z=−3、ay=2。
最低水準の訪問r≥q0を落とすと既存負Az例のz途中で負面積が出るため、仮定を黙って除かない。
受入は全量化子のLean theorem・逐語audit・full check。残余は最低水準がq0前にしかない場合。

### 次の局所入力: ブロックprefixの有限context（形式化前の仕様）

任意のf,n,a,βについてseg f 0 n=β++A^a、BlockWord βとする。
全t≤nで、接尾辞の密度から
`2*(n−t) ≤ 5*(Fw(n)−Fw(t))`（全項は整数cast）を示す。
その上でs≤n≤b、D≥0、Fw(b)≥Fw(n)−D、`5*(D+1)≤2*(n−s)`なら
`EndN f 0 b ↔ EndN f s b`を主張する。

chain: 窓の古い始点t<nではFw(t)=Fw(b)−1なので、n−t≤(5/2)(D+1)。
t<sなら半径条件に反する。逆向きは始点範囲の包含。
これは窓のmomentを近似せず、元のEndableを正確に保つcontext削減である。
Q自体や親Hを仮定しない。Dを固定した有限深さ用で、深さの上限を証明したことにはならない。

受入: 具体的な符号語の窓について両方向のLean theorem、逐語audit、全体検証。
使い道: D=4なら直前13clockでtailのEndableを完全判定でき、prefixの無目的な長さ走査を避ける。
13clock suffixを覆う最後のブロック列は長さ≤22（最大ブロック長10）で代表できる。
後者の有限文法の全suffix生成と、a_z≤3・深さ≤4のtail分類を別unitで検査する。
全体の深さ≤4、全体Q、未知の無制限分類を結論しない。

08:56以後の丸め監査: 一般半径は`5(D+1)<2((n−s)+1)`でも十分で、整数floorまで詰められる。
さらにD=4ではmass≤5と`length−mass=2*#S`のparityを併用すると接尾辞長≤11となる。
（長さ12ならmassは偶数かつ≤5なので≤4、密度2*12≤5*4に反する。）
従って深さ4の正確なcontextは11clockで足り、そのsuffixを覆うブロック代表は長さ≤20。
初期の13clockは安全な上界だったが最小の供給ではなかった。次のclassifierは証明後の11clockを使う。
半径の条件を落とすと`SSAAAASAAA S^8 A^6`のb=23で唯一の窓始点0を失う
（n=10,D=3、必要10clockに対して9clockでは不足）。直接和で全始点を照合済み。

### 08:58:41確認点（30分27秒）

- E-379（fresh-low Q）とE-380（exact prefix context）をPROVED-LEANとして登録。
  既存BlockSuffixPositivity.leanに追加し、statementを逐語監査。新規独立moduleを量産していない。
- 全体検証は404 build jobs・2663宣言の公理監査を通過。追加の独自axiomや禁止構文なし。
- 新しい独立edgeを得たのでC1を継続。Q-old-min有限制約はINFEASIBLE（q0=32,b=64）だが一般Qを昇格しない。
- R/旧minimumのcouplingはCONJECTURED。depth4とa_z≤3の分類に進む場合は、その二つを仮定として明示する。
- contextはk1前の11clockであり、k1以後の全tailを保持する。11clockだけの有限状態化ではない。

### context代表の網羅性も形式化する（実装前の補助義務）

任意のW≥0とBlockWord w（W≤length w）について、w=u++v、BlockWord v、
W≤length v≤W+9となるu,vが存在する。W=11なら代表長≤20。
既存block_firstの先頭ブロック長は1/4/10なので、全長がW+9を超える間は先頭を取り除き、
長さの強い帰納法で証明する。新しい文法を仮定せず、既存BlockWordをそのまま使う。
受入はLeanの全量化子付き構成。これはE-380の計算対象の網羅性を補うhelperであり、Qの新たな解決と数えない。

09:04以後の強化候補: 三つのatomのどのsuffixもBlockWordであるため、文法全体がsuffix-closedである。
これを既存BlockWordについて証明できれば、代表は長さWちょうどでよく、W+9の余りは不要となる。
実装前にatom Cのdrop1=`SAAAA SAAA`も`SAAA A SAAA`と分解できることを確認した。
受入は全suffixについてのLean証明。単に21個などの個数をデータから仮定しない。

### 09:12以後の局所入力: ブロック接尾辞の二次面積下界（実装前仕様）

候補BQ: 全てのBlockWord wについて `2*areaW(w)+2 ≥ mass(w)*(mass(w)+1)`。
空語も含む。全てのsuffixもBlockWordであるため、古い窓始点t<k1のprefix面積に同じ下界を供給できる。
SAAA A^jでは等号（全j≥0）と予想し、定数2のsharpnessを検査する。

chain: atom Aのappendは差`2area−mass(mass+1)`を保つ。SAAAは4mass−2、
tripleは12mass−2を足す。空prefixなら差−2、非空prefixならmass≥1なので差を下げない。
全体H/EqClassW/Qは使わず、実際の符号語文法の帰納だけで証明する。
反証pass: SAAA/triple/空語/Aとappend順序、BlockWordを落とすSSAAA（mass1,area−3）を照合する。

使い道: P2(t,b)のmass r=g−F(b)+1に応じ、古いprefixの面積は少なくともmax(1,r(r+1)/2−1)。
Q本体は変更せず、C1へ必要な面積下界をどこまで弱くできるかを診断する新入力。
「未証明のweighted Qを仮定しただけ」を進捗とはしない。受入は本下界とsharp familyのLean証明・意味監査・full check。
15分で非循環な証明ができなければこの方法を止め、未解決のまま保存する。

この入力により予定を開始5・C1活用50・局所入力30・監査15へ再配分（合計100）。
数学的な新情報が得られたための変更で、CPU待機を別の研究時間へ加算しない。

BQの等号caseも判定する: BlockWord wについて等号となるのは、あるj≥0で
`w=SAAA A^j` または `w=SSAAAASAAA A^j` の場合ちょうど、と予想する。
atom Aは面積defectを保ち、非空prefixへのSAAA/tripleのappendはdefectを厳密に増やすため、
最初の非A atomの後はAだけとなる。空語/Aだけは等号でない。
これが示せれば旧minimumの境界caseに入るprefix形状を二族に限定できる。
混合A·SAAA、SAAA·SAAAなどのstrict例と両sharp familyで反証passを行う。
Qを仮定した帰着を新成果に数えず、BQ unit内の15分上限を延長しない。

BQの実際の窓への消費形も固定する: prefix終端n、t≤n≤b、Win f t (b−t)なら、
r=Fw(n)−Fw(b)+1、Z=Ar f n (b−n)+(b−n)rとして `2Z≤2−r(r+1)`。
窓のmoment=0をnで分けた恒等式とBQから得る必要条件であり、それ自体をC1の排除とは呼ばない。
元Qは変更しない。r≥2ではZ≥2−r(r+1)/2を別に証明できれば古い窓を排除できる。
r=1は既存の面積≥1とZ≥0で処理する。整数の丸め・strict inequalityを監査する。

### 09:24〜09:25確認点

- 71 context分類の別Python監査が0.103秒で完了。全始点を後ろ向きmass/momentで調べ、mod4枝刈りもGも使わず、
  全46,674 nodeと19,950 guard endpoint、各cut数、全z候補、全min値が一致。NFAの別文法監査も一致。
- E-382をCOMPUTEDで登録。a_z=3、深さ≤4ならzはSASAAA/SSAAAA/SSAAAASA/SSSSAAAASAAAの4語。
  Qの最小1。最大state prefix長20（endpointの符号は別に選ぶ）。深さ4自体の証明やLean証明書ではない。
- E-381の二次面積下界・sharp family・等号二族・実窓の必要条件は全体検証済み。
  404 build jobs、2678宣言の公理監査が通過。
- R-negativeとpeak-fiveの各900秒制約探索はUNKNOWN。その設定の延長をSTOPPEDとし、数学的候補はCONJECTURED。
- 09:25:11からdeep-threeを実行。次はspectrum緩和とY-triangle、予算と終了時刻を維持する。

### 適応的なprefix代表（09:30以後、実装前仕様）

ブロックprefix終端n、有限の後半区間[n,B)、全u∈[n,B)でFw(u)≥Fw(n)−Dを仮定する。
あるs≤nが存在して、seg f s(n−s)はBlockWord、全u∈[n,B)のEndN f 0 uとEndN f s uが同値、
かつs=n、または`1≤Fw(n)−Fw(s)≤D+1`となることを主張する。

chain: 後半に終わるold windowがなければs=n。あればその全始点の最小sをfirst_markで選ぶ。
全ての窓はs以後から始まり、選んだ窓のmassと高さ下界からprefix suffixのmass≤D+1。
suffix閉性がそのsuffixをBlockWordにする。元のprefixの長さには依存しない。
Endable patternは保存するが、削除前のprefix不足d(n)=0まで自動で保存したとは主張しない。
この区別を数値counterへの持上げと探索完全性の監査に残す。

受入は存在するsと全endpointの両方向をLeanで構成すること。15分の上限は09:45まで。
これによりtail長N・終端d=1なら総S≤floor((N+1)/2)なので、old prefixの必要massを
floor((N+1)/2)+1以下の有限BlockWord族へ帰着できる（prefix不足の扱いは別監査）。
Qや全区間Hを定義した仮説として置かず、実際の窓の最小始点を使う。

### old areaの上界UQ（09:45前、実装前の仕様）

候補: 全BlockWord w、m=mass(w)で `4*areaW(w) ≤ 5*m*m−11*m+16`。
mass0/1/2を境界検査し、A·SAAA（mass3,area7）で定数16がsharp。
文法を落とすAAASSS（mass0,area9）は反例。
defect `5m²−11m−4area`はtripleのappendで不変、Aでは6m−10、SAAAでは4m−10増える。
低massだけを既存block_mass2と新しいmass1分類で処理し、その他は文法の帰納で示す。

使い道: 旧窓の必要面積A_old=−Zを上からも制限する。
BQと合わせてold spectrumの量化子を保存したscalar envelopeを与えるが、Qの未知下界はなお未供給。
受入は全量化子のLean証明・sharp具体語・意味監査・full check。09:55までに通らなければ登録せず停止する。

研究が続けられる間は、単位の終了だけで100分全体を終了しない。待つだけで実績を増やさず、
時刻・CPU時間・作業内容を分けて記録する。継続不能ならその具体的な外的・数学的理由を残す。

### 09:50 検証pass（新しい探索域へ移らない）

UQはsource checkを通過し、全体checkも404 jobs/2685 declarationsで通過した。
Y-triangleは120秒でUNKNOWN、深さ5のexact固定長80も900秒でUNKNOWN。
候補の数学的labelはCONJECTURED、同じ設定の延長はSTOPPED。
E-383の長さ1..32の全treeを、F/G・mod4を使わない独立C++で全件再検証する。
300CPU秒を上限とし、既定3900秒内。全counts/min値/候補語が一致することを受入とする。
新しい長さ・深さ・prefix範囲を追加しない。結果にかかわらず、以後は監査・引き継ぎへ移る。

### 09:52 検証結果と残余6分の紙上監査unit

N32/R17の独立全treeは2.53秒で完了し、125181373 nodeと全cut数・全候補・min値が一致した。
元の有限領域を拡張していない。full check/工具回帰も通過したため、残る新数学枠を次の紙上入力監査に再配分する。
問い: m≥2に対し、BlockWordのmass mで実現するareaは整数区間
`[m(m+1)/2−1, floor((5m²−11m+16)/4)]`の全体ちょうどか。
m=0は{0}、m=1は{1}を別扱いする。個々のold P2 signatureのspectrumを一様に特徴づけるための問いで、Q自体は仮定しない。
受入: 三atomの正確な再帰、m=0..7の明示集合、m≥8の区間間に隙間がない不等式と構成の完全な紙上chain。
反証passは既存の独立全語監査済みmass≤17の集合と一致させ、例外mass0/1を攻撃する。
09:58:14までに完全な両方向が書けなければCONJECTUREDのまま保存する。
Lean実装や追加CPU探索へ拡張せず、以後の10分は証拠・時刻・出典の記録に使う。

### 09:57 組合せの意味監査

E-382の全tail深さ4とE-379を二分して使えば、a_z≤3ではzの深さ4だけを仮定すれば全yを扱える。
新しいglobal minimumがyへ出たときはE-379、そのままならE-382の完了木。z長≤32ならE-383が深さを供給する。
証拠はCOMPUTED依存、未Lean。次の一様深さ4入力が通ってもa_z≥4の一般Qは残る。
このchainをQそのものを仮定したwrapperや中心命題の解決と数えない。

## 最終判定（時刻はhandoffで確定）

| 対象 | 証拠label / 判断 | 次の扱い |
|---|---|---|
| Q全体 | CONJECTURED | 旧minimum caseとa_z≥4が残る |
| fresh-low Q | PROVED-LEAN / E-379 | 元p基点、予算1、同じ符号語の最小値条件を維持 |
| prefix削減・suffix閉性・適応mass代表 | PROVED-LEAN / E-380 | 深さ供給とprefix不足を別義務にする |
| 二次面積上下界・等号二族 | PROVED-LEAN / E-381 | Qの未知下界を仮定した成果にしない |
| 71context全tree | COMPUTED / E-382 | 深さ4・a_z≤3、kernel証明書は未実施 |
| tail長1..32・任意長prefixの全tree | COMPUTED / E-383 | 全125181373 nodeの独立照合済み、上限を無制限へ外挿しない |
| 全massの面積spectrum | PROVED-PAPER / E-384 | 存在方向未Lean・人間レビュー未 |
| Az単独非負 | REFUTED、方法STOPPED | 元Dから新仮定を供給できるまで再開しない |
| 自由Endable tag | 弱化モデルの反例、方法STOPPED | 実際のQの反例とはしない |
| R/peak/deep/Yの有界solver | UNKNOWN、同設定延長STOPPED | 数学的候補はCONJECTURED |

source/model hash22件、全source snapshot419ファイル、別directoryでのG5/lint/protected/briefが通過した。
検証済みsourceは現在と同じ。朝の実績・並行CPU・親cycleを二重計上しない。
実時刻区間、実測CPU3425.57秒とその未計測範囲、commands、次の一問はhandoffを正本とする。
今回の新edgeを理由にC1を継続し、同じ障害で無変化のcycleとして加算せず、過去の停滞状態も日付でリセットしない。

最終の実時刻: 08:28:14〜10:06:27 JST、経過98分13秒。保存・監査を含み、CPUとの二重加算なし。
