# C1 Q 面積分解: 実行前protocol

- Session: 2026-10-22 08:28:14〜10:08:14 JST。今回の利用者指示による100分枠。
- Card: H-20261022-01。主目標と補助候補A/Yの全仮定はカードを正本とする。
- 初期CPU枠: 全実験の合計1200 CPU秒、単一計算worker、memory≤1GiB。
- discovery第1pass: prefix長LW=20、y長LY=32、最大60 CPU秒・70経過秒。
  目的はAz/Y/Zの各項の最小値と明示witnessを取得し、分解のどの下界が偽かを判定すること。
  旧語長範囲の再走を新しい数学的holdoutや上限拡大の成果とは呼ばない。
- 旧q.c/z2.cとの違い: d(b+1)≥1を課す本来のprefix領域と、枝刈り前の広い領域を別に記録し、
  最小値の完全な語・q0・k1・bを保存する。飽和counterは使わずoverflowなら停止する。
- 反例候補は別実装の直接符号和・重み付き和・全始点走査で再計算し、全仮定と結論の否定を照合する。
  強化prefix候補だけの反例は完成設定DのQを反証しない。
- holdout: discovery結果で進める候補を一つ選び、別の長履歴生成器と範囲・seedを凍結してから一回のみ。
  初回はまだ実行しない。母集団が空なら空検査と記録し、成功の証拠にしない。
- 紙上検討: 分解恒等式は成果ではない。AまたはYの反例が出たら一回だけ原因に基づく修理を許し、
  次に第一Z負化と非Endable Aの位置関係を評価する。
- 保存: source・実行時source hash・revision・dirty patch・argv・実測CPU/経過・stdout/stderr・完全性フラグ。
- 全ての処理は10:08:14までに終了。100分が経過したふりをせず、前回実績・今回の実績・待機を区別する。

## Discovery第2pass（08:33以降、実行前固定）

- 問い: Az<0の履歴で、Qのguardを満たすbまで進むとYとlevel補正がどう相殺するか。
  三項を独立に非負とする方法は停止し、`Az+Y≥0`という補正不要の強化案Bを反証する。
- 元のQの量化子は変更しない。Bは完成・IHを落としたprefix上の補助候補。
- sourceはarea_probe_v2.cpp。LW=28, LY=64、wall上限300秒、CPU上限310秒。
  新しく、Az<0母集団の母数、Z/Y/Az+Yの最小値・完全witness、最初のZ負化時の符号/Endableを採取する。
  全体のhorizon増加だけを成果とはせず、条件付き母集団が空なら空と記録する。
- この領域はdiscovery。旧範囲を含むため独立holdoutではない。first-negativeが出てもD全条件を別照合する。
- source hashとコマンドを実行直前に保存し、停止時complete=falseを残す。

## 独立生成holdout（実行前固定、今回一回限り）

- 凍結する候補: B=`Az+Y≥0`、R=`Az+max(h,0)(max(h,0)+1)/2≥0`（h>0）、
  元のprefix Q、Y≥0。Rのh≤0はQ(q0)を直接記録する。
- generator: holdout.cpp、SplitMix64 seed=0x20261022c1a5b17d、80〜384clockの履歴、8生成群を順に循環。
  一様語、A確率2/3、長いrun、ブロック語の局所変異、既知負Az motifの長い文脈、
  S/A run対、Endable優先の逐次生成、slackを1へ戻す逐次生成を区別する。
- 最初に各生成語のF/G/Endable/d/aを実際のP2条件で再計算し、全てのprefix-Hかつd(q0)=1のsplitを採用。
  q0以後はd≥1・非Endable A≤1が続く最長の範囲だけをチェックする。Endableなbの部分集合も別集計。
  完成Dや短い全区間IHを検査したとは呼ばない。
- 最大2,000,000語、CPU上限900秒（単一worker）、内部wall上限910秒、memory≤1GiB。
  CPU枠は初期合計1200秒内。全体と各生成群で採用splitとguardを満たすendpointの数を出す。
- 乱数生成は決定的。時間上限で止まれば実際に完了した先頭sample数とstateを保存し、
  その有限sampleの結果だけをCOMPUTEDとする。反例を得た場合は最初の語/全パラメータを保存して停止。
- 範囲は旧短語の全走査と重ならない長い完全語。ただし既知motif/既知ブロックを含むため、
  「全構造が未知」「一様母集団」「長さ384まで網羅」とは主張しない。
- raw output・実行時source/hash・argv・CPU・経過を保存。holdout結果を見て候補を変更したら、その結果はdiscoveryへ移す。

## 固定非Endable A予算の分類probe（実行前固定）

- 問い: a_z≤3の正のslack excursionに、Sが多数あるq0（d=1）やR<0が現れるか。
  単なる長さの延長ではなく、非Endable A予算を固定した分類を試す。Aが非Endableなら予算を消費し、
  実際のP2条件でEndableなら消費しない。自由tagモデルを混ぜない。
- prefixは(A|SAAA|SSAAAASAAA)*のうち長さ≤32。各prefixで実際にd=0・全prefix d≥0を確かめる。
  zの内部はd>0、非Endable A≤3、S≤128。q0はd=1の各endpoint。
- 目的量はa_z別の最大S、RとAzの最小値、完全witness。中断時は完了したprefix数とcutoff数を記す。
  S=128を越す枝は切るため、無制限の分類証明と呼ばない。
- 単一worker、wall590秒、CPU600秒、memory≤1GiB。残る初期1200CPU秒の枠内で実行する。
  source=budget_classify.cpp、コマンドとhashを実行前保存。これはdiscoveryで、先のholdoutを再利用しない。
- 計算中はRの紙上依存・自由tag反例の別pass監査を進める。完了か中断で判定し、無目的なS上限増加はしない。

## 08:50確認点: exact constraint探索へ切替（実行前の再配分）

- 固定A予算probeは590.31秒で打ち切り、1971prefixを完了したが全域は未完了。
  252億nodeの大半が予算超過で、S上限128までの死枝走査は費用に対する情報が小さい。上限延長はSTOPPED。
- 紙上・Leanでfresh-low部分場合を得たため、Qの残余を「全体の最低水準がq0前にしかない場合」へ絞る。
  次は語を順に延長せず、全P2のmass/momentとEndable同値を整数制約として同時に課す。
- CPU合計上限を1200秒から3900秒へ事前変更する。ユーザーの100分枠内で単一solver worker、
  1run wall≤900秒・CPU≤910秒、memory≤1GiB。新規探索は09:58:14 JSTまで、全処理は10:08:14まで。
  増枠の理由は新しく限定できた未知caseの制約探索。単なるlag/長さ延長を成果にしない。
- source=c1_constraints.py、環境は/tmpの独立venv、実際のpackage版と配布hashはinstall reportに固定。
  公式仕様: https://developers.google.com/optimization/install/python と
  https://developers.google.com/optimization/cp/cp_solver 。UNKNOWNをUNSATや証明と呼ばない。
- 最初に全長8の256語と既知の陰性対照で、全Endableが「Aかつ窓が存在」と同値であることを別実装と照合。
  Endableを都合よく選んだsubsetにしない。発見したSAT解は全始点直接走査で独立再計算する。
- 凍結する3目的（discovery、各一回900秒以内）:
  1. Q-old-min: prefix=SAAA, k1=4, q0=32, b=64、d(q0)=1、全(k1,b+1]でd≥1、
     a_p(q0,b+1)≤1、F(b)≤F(k1)、全体minimumはq0前のみ、Z(b)<0。
  2. R-negative: prefix=SAAA, k1=4, q0=80、d(q0)=1、内部d>0、h=F(q0)−g≥1、
     2Az+h(h+1)<0。完成D/yは仮定しない。
  3. peak-five: prefix=SAAA, k1=4, q0=80、d(q0)=1、内部d>0、内部にd≥5。
     これは「defect1 excursionのpeak≤4」という有限文法候補を反証する局所探索。Qと同値ではない。
- 目的ごとにSAT/INFEASIBLE/UNKNOWN、モデルhash、seed、worker数、時間・conflict・branch数・解を保存する。
  INFEASIBLEでもその有限パラメータの結果だけ。全D条件や短い区間IHの検証は別義務。
  一様な反例/新入力がなければ予算で止め、同じ目的の時間延長・同じ上限拡大を自動実行しない。

## E-380後のcontext分類（実行前固定、solverと同時実行しない）

- 仮定: ブロックprefix、zのa_z≤3、d_z>0、q0でd_z=1、全[k1,b]でFw≥g−4。
  yは元のp基点で非Endable A≤1、b+1までd≥1、Qのguard F(b)≤g。
  深さ4・a_z≤3は明示的な制限であり、完成D全体に供給済みとは呼ばない。
- E-380の11clock削減を使う。全ての長さ11のブロック語suffixは、それを覆う最後のブロック列
  （長さ≤20、各ブロック長≤10）で代表できる。短いprefixはそのまま。生成・全suffix一覧を保存する。
- source=context_classify.cpp。z/yのA・S分岐を実際の全P2始点で評価し、深さ・個数・正slackだけで枝刈りする。
  S数や語長の数学的cutoffを置かない。実装のstack保護512tail clockまたはwall120秒に達したら
  complete=falseで全検査を停止し、無制限分類の完了とは呼ばない。
- endpoint bの判定後に次のF(b+1)が深さ制限を外れた枝を止める。深さの量化域はbまで、d/ayの域はb+1まで。
  元のq.cのような枝刈り前の広い領域を無言で混ぜない。
- 目的: 全代表でQ、R、a_z別最大S、最大到達語長、zの全候補を取得。
  complete=trueかつ保護cutoff未使用なら、宣言した仮定の有限探索木を最後まで調べたCOMPUTED結果とする。
  それをLeanの定理、全深さ・全a_zのQの証明とは呼ばない。
- CPU≤130秒、wall≤120秒、単一worker。3900CPU秒合計内で実行。source/hash/argv/出力/計時を保存。

09:05の形式化後、BlockWordの全suffixがBlockWordであることをLeanで確認したため、
代表生成は長さ≤11までに縮小する（長いprefixの代表はその11clock suffixそのもの）。
先の≤20生成は安全だったが不要。実行前のsource更新であり、結果を見て範囲を狭めたものではない。
NFAの別実装で、全到達状態から11文字を読んでblock境界に終わる語の集合と一致することを照合する。

## 50分確認点後の追加二目的（実行前固定）

- context分類は全71代表、46,674 nodeで完了。保護cutoff未使用、Q最小1。
  次に必要なのは深さ4の供給なので、a_z≤3なのに深さ5へ達してd=1に戻る語を直接狙う。
- 旧c1_constraints.pyは実行中のsource hashを保つため変更しない。追加modeはコピーの
  c1_constraints_v2.pyに凍結し、同じE⇔A∧∃P2の実装・校正を使う。
- deep-three: prefix=SAAA,k1=4,q0=80、全(k1,q0]のd≥1,d(q0)=1、
  a_p(k1,q0)≤3、min_[k1,q0] F≤g−5。完成D/IHは未検査。
  wall900秒・CPU910秒以内、単一worker、memory≤1GiB。SATなら深さ候補の反例であってQの反例とは限らない。
- Y-triangle: prefix=SAAA,k1=4,q0=32,b=64、Q-old-minと同じ正slack・ay≤1・old-only minimum・F(b)≤g。
  h=F(q0)−F(b)≥0、`2Y−h(h+1)<0`を狙う。Y≥h(h+1)/2という独立な補助案の反証で、
  Q自体やR_C1の反証とは区別する。wall480秒・CPU490秒以内、単一worker。
- peak-five→context-tree独立監査→v2校正→deep-three→Y-triangleの順。新しい探索を同時実行しない。
  UNKNOWNならその目的を止め、同じ設定で時間を足さない。09:58:14に新探索を止め、最後の10分は保存・監査。
- 合計CPU3900秒は維持。実行前に残枠と実時刻を確認し、最後のjobの時間を短くする必要があればその理由を先に記す。

## BQ後の局所探索候補: 古いprefixの面積spectrum（実行前固定）

- BlockWordはsuffix-closed（Lean済み）。mass rの全BlockWordのarea集合S_rは、
  S_0={0}からatom A:(+1,+m+1)、SAAA:(+2,+4m+2)、triple:(+4,+10m+9)をappendする
  mass順DPで正確に生成できる。各areaの具体的な語を保存し、BQとequality classificationに照合する。
- 目的は「個々のold windowでこの正確なspectrumを満たす」だけで深さ5のdefect1例を除けるか。
  old windowの共通prefixを別々に選べる緩和モデルであり、SAT解を実語の反例と呼ばない。
- source=old_spectrum_relax.py。tail長N=32、d(0)=0、内部d>0、d(N)=1、非Endable A≤3、minF≤−5。
  local P2は全て正確に数え、old flagだけを追加できる。各old flagはr=1−F(b)≥1と
  required area=−Z(b)∈S_rを満たす。EはAかつ（local windowまたはold flag）と同値。
- d(N)=1からmass(N)=a(N)−1≥−1なので総S≤floor((N+1)/2)、必要rは≤17。
  このR上限をDPへ使い、語長の都合で真のold startを落とさない。
- 最初に既知prefix SAAA/tripleの実際のtail Endableが埋め込めることと、mass1/area8の偽old flagを
  tableが排除することを校正。SAT時は各old flagの具体的なBlockWord witnessを出し、
  共通prefixへ持ち上がるかを別監査する。持上げ未確認なら未確認と明記する。
- spectrum緩和はwall solve240秒・process CPU270秒以内。Y-triangleの上限は480→180秒へ縮める。
  新しいBQ/suffix閉性を直接使う入力の情報価値を優先する再配分で、合計3900CPU秒は維持。
  deep-three→spectrum緩和→Y-triangle、全て単一worker、09:58:14までに新探索終了。
  同じ緩和モデルの無目的な延長・修理はしない。

SAT時の持上げ監査はcommon_prefix_lift.py、CPUの残枠を確認して最大60経過秒。
local窓が既にあるclockの冗長なold flagを消してから、必要なold windowの最古の始点でprefixを切る。
suffix閉性より、その語はBlockWordでmass≤max(required mass)となる。従ってそのmass以下の全BlockWordを
列挙し、個別signatureの同時成立と全tail Endable patternを照合する。
共通patternがあってもprefixのd=0・非負性が未供給なら実際の数値設定の反例へ昇格しない。
全列挙未完了なら「持上げ不能」とは呼ばない。完成Dや全真部分区間IHはこの監査でも未検査。

## 適応mass代表を使うexact探索（09:32、実行前の優先順位変更）

- 最古のold window始点を使う共通prefix代表を形式化中。後半で高さ下落≤Dなら必要prefix mass≤D+1。
  残す語はBlockWord（suffix閉性）。Endable patternは全後半で保存し、prefix不足の保存は別に確認する。
- q0−k1≤32・d(q0)=1ではmass=a_z−1≥−1なのでS_total≤16、全endpointで下落≤16、代表mass≤17。
  よってmass≤17の全BlockWordを使い、任意に長い元prefixを含む、長さ≤32のtailをexactに探索できる。
- source=prefix_mass_search.cpp。全代表でprefixの実際のd=0・非負性を確認し、失敗ならincompleteとして保存。
  tailのa_z≤3・d>0、1≤tail長≤32、d(q0)=1、minF≤g−5の反例を探す。
  S>16と、残りclock数ではd=1へ戻れない枝だけを追加で切る。どちらも終端条件からの必要条件。
  n=32の固定一長だけでなく、全てのtail長1..32を対象とする。
- wall240秒・CPU250秒、単一worker。反例が出れば全F/d/AN・全始点直接和で独立監査。
  完了しても有限tail長の結果であり、無制限の深さ供給やQ全体を証明したとは呼ばない。
- 新しいLean入力によるexact共通prefixを優先し、順序をdeep-three→exact mass探索→spectrum緩和→Y-triangleへ変更。
  spectrumは240→60秒、Y-triangleは180→120秒へ縮める。必要時の持上げ監査は最大60秒。
  合計CPU3900秒と09:58:14の新探索終了時刻は維持する。語長上限を増やすための変更ではない。

exact mass探索の前にN=12,R=7の小さな全域を、F/G/mod4を使わない別Pythonの直接mass/moment・
直接面積和で照合する。R=17のprefix族自体は全語を別生成し、mass別個数・d=0・prefix非負性を監査する。
小さいtail域の一致を大きいtail域の独立な全検証とは呼ばず、N=32結果の限界に区別して記す。

## 09:50 全長32の独立検証（探索域は拡張しない、実行前固定）

- 既存E-383の125181373 node全treeを独立したC++で再走査する。新しい数学的領域を探索しない。
- source=prefix_mass_independent.cpp。prefixはmass昇順の集合で別生成し、窓は後ろ向きの符号和と重み付き和を全始点で直接計算する。F/G式・mod4削減は使わない。
- 面積は保存した全levelの直接和。全node/cut数、全prefix counts、全az分類・最小値・語集合を元JSONと完全照合する。
- argv: /tmp/recaman-c1-prefix-mass-independent 32 17 300。wall300秒、CPU300秒、単一process。
  既実測CPU約3423秒+300秒≤3900秒。制限に達したらincompleteのまま保存し、独立全検証済みとはしない。
- 校正は元sourceとの小範囲N12/R7の全counts一致。N32も一致した場合だけE-383の監査範囲を更新する。
