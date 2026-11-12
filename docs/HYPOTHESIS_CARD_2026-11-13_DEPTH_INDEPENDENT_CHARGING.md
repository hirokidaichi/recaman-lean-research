# Hypothesis card: 任意深さに消費できる課金原理の診断

- ID H-20261113-02
- Owner Codex; created 2026-11-12 user-directed planning update
- Work state unstarted; primary general-principle exploration/falsification
- Evidence: 新しい数学的証拠なし。次回setupで個別候補のexact statementと既定labelを凍結するまで実装しない。
- Parent 11/12 DAILY、E681/E674、protocol 1.8、一般化tracker

## One bounded decision question

同じ元履歴の二つ以上のactual供給窓について、E681の面積評価とE674の高さ別課金を
**任意深さでも消費できる重複制御**へ接続する最小の新edgeを、証拠付きで得られるか。
最初15分はこの機構の新edge又は反証を判定する。候補作成・既存式の包装だけなら一般化進展なし。
「C1を証明する」を一unitにせず、具体候補一つのaccept/refute/stopを決める。

## Domain and statement-freezing contract

対象候補の共通domainは任意f:Nat→Bool、n,a,b,j,D:Nat、w:List Bool。
BlockWord w、seg f 0 n=w++A^a、n<b、全n<=i<=bでFw n−D<=Fw i。
必要なら全非空prefixで元EndN0件数+1<=S数、最後j個Sと元EndN0(b+j)を明記する。
run数、上昇高さ、全oldmass、源以前prefixに固定上限を設けない。各Winは自分のsource/長さを持つ。
Dというbinderだけで一般性を主張せず、使用しないdomain仮定は除いた候補を明記する。

次回setupで既存portfolio/反例を検索し、既存定義のどの実写像・請求を使うか選ぶ。
**新候補の不等式/負荷上限/相殺項を一つだけ、全量化子・依存込みで書いてから**そのunitを開始する。
この計画書は未定の負荷定数が存在すると主張するPropではない。未固定でLeanやCPUを起動しない。

## Generalization contract and acceptance

- 元actual EndN f 0/freeを維持し、低い全Aをfreeへ置換しない。
- 同freeの複数請求をどの写像/実cNで数えるか、最大負荷又は相殺する境界負債を明記する。
- 深さDが増える費用をどの証明済み項が払うか示す。
- 消費する具体的な無重み件数不等式又は元履歴を保つ深さ操作を指定する。
- 任意Dの新辺の完全PAPER/Lean証明、又は一般機構を破る正確な反例/no-goで判定する。
  有限計算だけならCOMPUTEDで範囲を固定し、無制限の不存在証明にしない。
- E681/E674の再引用、E675の全count輸送の単純再実行、D6→D7の検証は受入でない。

## Known inputs and falsifier

E681の同元内部窓area式とE674の全高さ供給<=低い全A重みはPROVED-LEAN。
E675幾何重み会計はPROVED-PAPER、全count輸送H38/RはSTOPPED。
E642の重複課金、E660幅4/A5/free2、E598の任意run供給非有界族を該当候補への既知反例として使う。
既知反例の再発見を新進展に数えず、C1/実orbit反例へ昇格しない。
境界D0/1、同freeを異高さで再使用する履歴、source=n、旧/局所source混在を攻撃する。
新計算のdiscovery/holdoutは別に凍結し、未見と確認できない履歴をfresh holdoutと呼ばない。

## Allocation and switching

研究・監査100分の予定は一般化60/局所30/独立監査10。setup10/handoff10は別枠。
主課題は最初30分、15分で判定。新辺/一般機構の反証がなければ同機構を延長せず、残りを別機構へ。
局所副課題[H-20261113-01](HYPOTHESIS_CARD_2026-11-13_SECOND_CLOCK_FIVE_SOURCE.md)は総30分上限。
後半一般化30分のうち25分以上は、重みを外す際の必要な補正、深さ操作のactual輸送、又は
広いhistoryモデルに不足する軌道条件の監査から、前半とは異なる機構を一つ選ぶ。
名前だけ変えた同じ未知仮定を別機構と呼ばない。各候補式と停止条件を先に凍結する。
残り5分で接続契約と局所側/一般化側の判定を記録する。局所成果で一般化時間を消費しない。

一般化側進展なしが親cycle二回連続なら次回20/70/10。新指標の過去は未評価、遡及resetしない。
unit停止でも日次を早期終了せず、有用な別機構/必要仮定監査へ切り替える。

## Resource and stop discipline

CPU探索予算は当初0、実行前の契約/累積計測/費用/独立holdout凍結を省かない。
個別Leanは-j1/-M512/10CPU秒per-process/20wall秒、一修理。独立数学pruning/小完全certificateと
同512MB測定改善なしに旧STOPPEDを資源/tactic/import/splitだけで再開しない。
H49/Rの採用外を重点変更で復活させず、元prefixのreset/結論の仮定化/dummy wrapperも不可。
G1–G5/保護claim/資源上限を維持し、07:45以後は検証・保存・終了報告へ移る。
