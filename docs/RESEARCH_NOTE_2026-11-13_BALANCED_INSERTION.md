# 深さ操作のsource時計とbalanced insertion（2026-11-13）

## 結論（研究中）
mass0/area0の挿入だけでは、元actual EndN/freeを輸送できない。具体例は個別Lean512MBで認証。さらに、**任意の固定非空mass0語**について、旧positive履歴の実供給を壊す明示反例がある。後者は以下の全量化紙上証明、未Lean・人間レビュー未。一般C1の反証ではない。

## 選択窓の正確な輸送式
元窓をcutまでのuと残りvに分け、mass(z)=0の語をcutへ挿入する。既存area appendから

area(u++z++v)=area(u++v)+area(z)+|z|*mass(u)。

mass(u)は元sourceからcutまでの高さ差。zのmass0/area0でも、sourceとcutの高さが異なれば元area0を保存しない。非空の同一zで二つの異なるsource高さのarea0を同時保持することは不可能である。area(z)を調整しても二つの補償式を同時に満たせない。BalancedInsertionAreaの全長Lean statementはこのheight agreementと、source高さ=cutの場合の**一件の窓**のmass1/area0検査の保存である。元EndN全体やfreeの保存を示していない。

## 元actualの具体反例
旧SAAAの最初S直後へz=ASSA（mass0/area0）を挿入すると、新語SASSAAAAとなる。旧target3は元EndN0だが新target7は非EndN0。両側target以前の全prefixは元actual正不足、target高さは同じ1、深さは旧1→新2。旧prefix free2、新prefix free3。さらに旧clock2のfreeは挿入後の対応clock6でactual供給へ変わる。挿入部の文字を数えるだけで旧freeをそのまま輸送することはできない。

BalancedInsertionCounterexample.zero_mass_zero_area_changes_original_endabilityを512MBで個別受理。新sourceの生成も旧sourceの消失も考慮し、対応する旧target/sourceを切り捨てない。標準orbit到達を主張しない。

## 固定balanced wordによる全履歴輸送のno-go（PROVED-PAPER）

### 全量化子と構成
任意の有限±1語zについてL=|z|>0、mass(z)=0とする。B=area(z)は任意整数でよい。d=L+|B|+2>=3とする。

W_d=S^(d+1) A^d S^(2d-2) A^(d+1)、q=5d-1、c=4d-1、t=d。

元f=finiteSign(W_d)、新gはW_dのcut cへzを挿入した有限語のfiniteSign。元target qと新target q+LはいずれもA。空BlockWord境界0を用い、全historyと元原点0を保持する。

### 旧sourceを尽くす
F(q)=1-dなので元Winのsource高さは-dに限る。四runの歩みを追うとq以前でその高さの時計は

d、d+2、3d、5d-2

の四つで尽くされる。これらからqまでの面積は順に

0、1、1-(d-1)^2、1。

確認にはSAA ++ (A^(d-2) S^(2d-2) A^d)を使える。括弧の語はmass0/length4d-4/area=-(4d-4)なのでmass1/area0のSAAへ追加してもarea0。二番目は初期一Aのarea1に同じ語を追加した形。三番目はS^(d-1) A^dでarea=1-(d-1)^2、四番目は一A。d>=3で零は一番目だけ。従ってqは元actual EndN0でsource t=dが唯一である。

### 挿入後の旧sourceと新source
cutの元高さは1-2d。挿入はmass0だから、元時計をcut以後でLずらせば全旧高さとtarget高さは同じ。最初三sourceはcut以前、最後source5d-2はcut以後にある。
cut以前sourceの面積変化は共通で

Delta=B+L*((1-2d)-(-d))=B-L(d-1)。

d=L+|B|+2、L>=1からDelta<=|B|-(d-1)<=-L-1<=-2。元三面積0/1/非正に加えると全て負で非零。cut以後sourceは自分の窓がそのまま平行移動されarea1を保つ。

挿入語内部の全高さは1-2d+L以下（±1語のL歩なので最大上昇<=L）。d>=L+2から1-2d+L<-d。従って元target高さ1-dへrise1する新しいsourceは挿入内部に存在しない。元source四つと新内部sourceを尽くしたので、新target q+Lは**非EndN g 0**。

### 両側のactual正不足（旧0<k<=5d、新0<k<=5d+L）
旧語の全非空prefixは高さ<=-1。最初S-run、最初A-runの最大-1、第二S-run、最後A-runの最大2-d<=-1を見ればよい。新挿入内部も高さ<=1-2d+L<=-d-1<0。その他の高さは元と同じ。両側とも全非空prefixでS-A=-F>=1、元EndNはAに含まれるからS-EndN>=1。これは宣言markではなく元actual countの正不足を内部供給している。

### 意味と停止
よって「一つの固定非空balanced wordをどのpositive履歴にも挿入してEndNを運ぶ」という機構はREFUTED。area0語はその特殊例であり、areaの調整だけでも普遍的には直せない。全z証明はPAPER、有限反例のkernel受理を全zのLean証明としない。

否定した量化子は∀z≠empty,mass0:∃history,cut:old actual/new nonactual。historyに応じてzやcutを選ぶ条件付き操作、元sourceを変える輸送、新sourceを明示課金する操作、全射性そのものは否定しない。選んだ旧targetの直前はAで最後S-gap0、最初Aはfreeなので元fullgapの反例ではない。

次consumerは、履歴に依存したsource高さ/面積条件と新source負債を同時保持する操作。単なるmass/area中立性や一件の窓の保存から元free保存を結論してはならない。

## Independent falsifier receipts / resource scope
全zの証明は上の四時計分類と高さ排除。有限検算は別に、長さ2/4/6/8/10/12の全balanced語1274（うちarea0は68）をreverse加重和で、長さ14/16の各32語（seed2026111306）をprefix-height/area方式で検算。全例で旧唯一source=d、新sourceなし、両側negative-height barrierが一致。最大d50/52。既存historyの未見性は確認せずglobally fresh holdoutとは呼ばない。
SPLICE_PROTOCOLを先に固定し、当日8CPU秒の未使用分から4秒を明示再配分。worker実測reverse .082469 / affine .036625秒、controller .001531/.001445秒。数学worker累積2.903377秒、CPU探索とLean検証は別。全argv/sourcehash/dirty revision/終了receiptは当日packet。

## Fresh-origin counterexample and single-window limitation
旧SSAA→新SSASSAAA、target3→7では元非EndNがactual EndNへ変わる。cut2のsource-heightは同じで、その旧一Aのarea1も挿入後area1を保つが、内部clock4のSAAが新供給を作る。従って一件の窓を正しく輸送しても元EndNの全source集合を輸送したことにはならない。この方向もkernel認証済み。

## Existing mechanisms kept separate
既存InitialSeparatorTrimは全A予算Bから初期SをC>=2B-1まで残すactual/free輸送である。今回の中立挿入no-goはその条件付き初期S trimを反証せず、旧停止jobの再開理由にしない。一般depth操作には消えるold sourceと生まれるnew sourceを同時に会計する条件が必要。既存append恒等式そのものを新しい一般化進展として独立計上しない。
