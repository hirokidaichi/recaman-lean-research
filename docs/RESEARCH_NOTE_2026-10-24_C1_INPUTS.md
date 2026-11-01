# 2026-10-24: C1の供給連鎖・共通prefix入力

結論: r4の全分類は未証明のまま。ただし、実語のS-gap圧縮、明示16終端語から先のQ、
無制限run族の供給制約、同じprefixの低mass情報を高々10代表へ縮める入力をLeanで得た。
大規模r4表の検証失敗は隠さず、E-388はCOMPUTEDを維持する。
数学的な中心の残余は、a_z≤4から明示16語への全包含と一般a_z≥5。
C1/Q/H/SL全体、C2/F/TS、全射性を解決したとは主張しない。

今回の進展は二つある。一つは「途中でどの形へ到達するか」と「その後どうなるか」を分け、
明示した16形から先では、どれほど長い将来を考えても必要な面積不等式が成り立つと確認したこと。
残る入口の問題は、a_z≤4の全ての場合がその16形に入るという証明である。

もう一つは、同じ過去を各窓で共用する制約を、mass3/4について10個の代表で正確に扱えるようにしたこと。
これにより、別々の窓に都合のよい過去をそれぞれ選ぶ緩和を狭める根拠ができた。
実際にr4の探索がどれだけ小さくなるかは、次の研究単位で測定する。

C1の証明済み領域の境界はa_z≤3のままで、a_z≤4の分類と一般a_z≥5が残る。
今回の入力は、その残りを攻めるための数学的な部品である。C1が完成した後も、
全体のSL/Hへ進むにはC2やTSなどの残余を別に閉じる必要がある。

## 1. 何が証明できたか

Aは加算、Sは減算。free Aは元の基点からEndableでないAであり、全Aとは異なる。
全ての実語定理で同じf/元基点を保持する。Nat clock版の基点0をInt元pへ移すadapterは
独立結果へ計上しない。人間レビューは未実施。

| 証拠 | 証明した入力 | 明示的な制限 |
| --- | --- | --- |
| E-390 PROVED-LEAN | 任意S-gap jをmin(j,19)へ写す実A0/A1 simulation | 次A直前の全A≤10等を仮定。全長A上限ではない |
| E-391 PROVED-LEAN | 明示有限terminal checkとfuture free A=0から任意長futureの全A=0 | checkが真である具体語/族を別途供給する |
| E-392 PROVED-LEAN | 明示16rootからの任意長/深さfuture Qとold P2排除 | a_z≤4から16語への分類は未供給 |
| E-393 PROVED-LEAN | localSupply(S^m A^r S^j) iff r=2(j+1), j+1≤m。長いSならactual EndNも分類 | actual iffにはr≥1,m≥2r−1と実endpoint Aが必要 |
| E-394 PROVED-LEAN | 同じprefixでmass3/area5と7は共存しない | mass3に限る。area6との併存は排除しない |
| E-395 REFUTED | 第4free後の供給A≤2という強化案を既知実例で棄却 | 終端不足4のprefix反例。親C1/Qの反例ではない |
| E-396 PROVED-LEAN | 具体w0=S5 A3 S4 A2後、future free0なら追加全A≤5 | 6nodeだけ。一般AN4のrankではない |
| E-397 PROVED-LEAN | k≥1,m≥4k+1のS^m A^(2k)後、future free0なら追加全A≤1 | run形と十分長いSを仮定。最良閾値ではない |
| E-398 PROVED-LEAN | 同じprefixのmass4二suffixの面積pairを制限 | 全massへの一律な両極値排除は偽 |
| E-399 PROVED-LEAN | 全mass3/4 suffixを同じ10候補代表へ保存し、必要mass3/4の実old窓/endpoint A付きEndNを全clockで同値化 | mass≥5や全Endable historyは保存しない |

G5逐語statement auditはE-390〜394/E-396〜399。全てのPROVED-LEAN行はAudit登録し、
全体check（408jobs、2782宣言、公理はpropext/Classical.choice/Quot.sound以内）を通した。
生成元・未追跡sourceもpacketへ凍結し、make briefとCURRENT_FRONTIERを同期する。

## 2. C1への接続と残る辺

```text
padded BlockWord prefix -> E-378の旧側面積が正
Q: tail面積が非負   -> old P2の総面積0と矛盾 -> C1

az<=3 -> E-386の全長8語/深さ4 -> E-387の任意future Q （既に完了）
az<=4 -[未供給の分類kernel]-> 明示16語 -> E-392の任意future Q
                                    深さ4外はE-379へ接続
az>=5 -[一般機構未解決]-> Q
```

E-392は後半の数学・kernelを先に閉じた。前半の分類を仮定として隠さない。
E-390は前半を有限に表す正しさを供給したが、その全12837状態をkernelで検査する方法が失敗した。
E-393/E-396/E-397は列の長さを増やす探索ではなく、供給が止まる理由を記号的に与える。
E-394/E-398/E-399は窓ごとに好きな旧prefixを選ぶ緩和を、同じprefixへ結合する別の入力。
これらが一般r4や任意rの全tailを覆うことは、まだ示していない。証明の割合は算出できない。

## 3. 供給連鎖と反例の意味

既知E-389のprefix ASAAA、tail S5 A3 S4 A4 S A3を再解析した。
全tail A10/free A4、全正不足、終端不足4。最後のfree後にAA S AAA、計5個の供給Aが続く。
全始点P2を独立reverse momentで確認。これは「高々2段で止める」計画を反証する。
元の語は新発見ではない。26候補のため規定の後半holdoutは0件、88実prefix/tail pairを検算。
有限モデルの最大5を一般上界へ昇格しない。

この具体motifだけは6node/次gap 0,0,1,0,0で閉じる。無制限gapはE-389で先に有限化し、
最後のnodeに供給がないことをkernel照合。最初のAへの帰納で任意future長を覆う（E-396）。
実prefix ASAAAで5が達成されることは独立有限検算であり、Lean存在定理として登録していない。

三runの式からr奇数ならlocal供給は不可能。十分長いSでold供給も消える（E-393）。
r=2kなら最初の供給gapはk−1に固定される。その後の語
S^m A^(2k) S^(k−1) A S^jについて、先頭S内からのmass1 suffixの面積は
(4k+2)j−4k+1となり、j0では負、j≥1では≥3。最初のA内からの面積は
(k−1)^2+2kj+j²+1≥1。残りの始点は奇数三run/単峰なので排除する。
m≥4k+1ならold個数障壁も破れ、以後の供給Aがない（E-397）。

## 4. 共通prefixは単純な「両極値排除」ではない

mass3はAAA/SAAAA/ASAAA（面積6/5/7）。面積5と7は異なる等長suffixなので共存しない。
mass4はAAAA/AASAAA/ASAAAA/SAAAAA/SAAASAAA/SSAAAASAAA（面積10/13/11/9/12/9）。
許可される異なる面積pairは無順序で{9,10},{10,11},{9,13},{12,13}だけ。
特に元のtrip語SSAAAASAAAは全体area9とsuffix AASAAAのarea13を同時に持つ。
「全massで両極値は共存しない」という一般化は採らない。

任意のBlockWord prefixについて、上の9候補の実suffixがなければ空語、あれば最長の一つrを選ぶ。
全候補のsuffixは長さ順に比較可能なので、同じrが全mass3/4語の所属を双方向に保存する。
明示10候補の長さ≤10とjoint profile相異をkernel検査（E-399）。
これは基点を途中へ取り直す操作ではない。元の基点からのEndNは保持し、
未来のold P2に必要なprefix語情報のうちmass3/4だけを共通rへ表す。
07:44までにこの同じrを全future clockで保持する実old窓の同値、実endpoint A付きEndNの同値もLeanで供給した。次の最弱edgeは、この正確な低mass判定を固定代表r4モデルに使うこと。

## 5. 失敗した方法と再開条件

r4 A-event graphは12837状態/513480 tagged case、最大全A10/16endpoint候補。
独立reverse/DFSで全状態/edge、928の長gap対照が一致した（COMPUTED）。
全表/関数block/Nat block/state-edge列分離のkernel検証は約11GiBまたは事前4GiB上限で自己processを停止。
停止理由とPID/argvはpacketのvalidation-result群へ保存し、未検証表は.lean.txtとして隔離。
数学的述語は弱めず、無条件の分類を未供給なTable仮定で包むsourceもactive Leanから除いた。
大規模一括decide法はSTOPPED。時間・メモリ増加だけでは再開せず、
新しい数学的quotientや実測で資源を減らすcheckerが得られた時だけ評価する。

初期CPU探索0を実行前に120CPU秒へ再配分。探索5jobのuser+sysは丸め表示で合計約6.66CPU秒、
wall約6.73秒。検証/Lean/記録は別。停止したvalidationのCPUが一部未取得なので総CPUは未確定。
実績wallへCPUを加算しない。最終実時計は当日DAILYとclosed journalを参照。

## 6. 旧prefix代表との比較監査

E-380は全futureが深さ4内という条件付きで、k1直前11clockを保持すれば全Endableが不変になる。
E-382の71代表は、その既に深さを仮定したQ領域の計算入力だった。
E-399の10代表は深さを仮定せずmass3/4のsuffixだけを同時に保存する。
従って旧11clockの全history削減を再証明しただけでも、全prefixを10状態にした定理でもない。
深く下がるold窓では必要mass≥5が残るため、10代表で全P2を判定する実装は不正。

まだ新しいr4 graphへ10代表を投入しておらず、r4の状態数や実prefix候補が減ったという計測はない。
次unitは既に証明した同じrのactual EndN同値を使い、固定代表r4モデルで従来緩和から具体に何を除けるかを評価する。
この評価が失敗してもE-399の定理は保持し、そのモデル改善方法をSTOPPEDと区別する。

## 7. 07:45前の最終接続（H13、E-399拡張）

同じrを全b>nの外で選ぶ。R=1+F(n)−F(b)が3/4なら、
実old窓がある iff rにsuffix vがあり mass(v)=R、area(v)=−Ar(n,b−n)−(b−n)R。
前方向は実old prefix suffix、逆方向はrが実prefix suffixであることからvを実時刻n−|v|へ戻し、
massとarea splitでWinを復元する。さらに実endpoint Aの下でEndN iff local窓またはこのold条件。
どちらも全clockで同じrを共有し、元0基点を保持する。mass≥5/全historyの同値ではない。

この低mass領域ではfalse tagの剪定も正当化できるが、S=19の飽和状態のtrim語から実tail massを
計算して適用してはならない。飽和後のold不在はE-385、localのtrim正当化はE-390で別に扱う。
実モデルの候補削減は次unitで計測し、未計測の有効性を主張しない。
