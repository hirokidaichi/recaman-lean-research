# 週間研究報告: 2026-09-18〜24

01:00枠では既存E-360 Q/Wとall-short U削除系の記載を独立監査し、01:30枠では
後半H-02/H-03/H-05の限定意味監査と総合未完了、H-04の限定反例・停止範囲を整理した。
これで既存確立済み範囲と後半候補・反例・未監査義務の記載案は揃ったが、週間全体の
最終停止・再開判断はまだ未完了である。対象版と判定は
[01:00監査](adversarial_audits/H-20260917-01_20260924_0100.md) と
[01:30合同監査](adversarial_audits/H-20260920-02_20260924_0130.md)、引き継ぎは
[9/24日次記録](RESEARCH_HANDOFF_2026-09-24_SOL.md)を参照。
新しい研究Lean・登録・昇格・予約延長は行っていない。

## 確立済み部分: E-360 の短い緊密集合と削除系

今週確立できた最大の主張は、周期長の上限を外した一方で lag を短い三種に限定した局所結果である。
E-360 の最終Q `short_tight_avoids_ss2_donor` は、任意の `p>0` と周期符号語 `e` について、重複のない
緊密リスト `B` の各要素が `p` 未満のcurrent-A位相であり、その窓が最小P2かつ
`lag in {3,7,11}` なら、最小lag-11・SS=2 donorの真の最古S位相が `N(B)` に入らないことを
`PROVED-LEAN` とする。pには上限がない。ただし任意lagではなく、lag 15以上の要素を含むBには何も言わない。
ambient `U`、仮定Hall、正driftは最終Qの仮定ではない。短窓selectorからBの全sublistのHallを内部で導く。

局所Wは別の読み方が必要である。`w1_owns_oldest` と `w1_next_addition` は、周期性から直接出る無条件定理
ではなく、`OwnerFamily` の4フィールド `window/addA/own_mem/onto` を仮定し、w1メンバーがoffset 7の
最古Sを所有し、その次符号がAであると述べる条件付き定理である。周期的な緊密Bへ使うときは、
`p>0`、周期性、nodup U、U上のHall、`B.Sublist U`、緊密性、範囲内current-A、最小P2
lag 3/7/11からE-358/E-359の構成でOwnerFamilyを実現するのが現登録証明の適用経路である。
この依存は現証明の説明から省かないが、OwnerFamilyの実現方法として数学的に唯一とは主張しない。
`ownerFamily_of_minimal` と `tight_owner_family` は既存依存の抽出であり、E-360の新規性には数えない。
E-351の `aas_after_w1_forced` は `e(u+1)=true` に加え、未来位相 `w=u+2`、`w in U`、
`lag w=3` 等を仮定して `w in B` を結論する。従って、これをWのnext-A結論の証明へ逆用していない。

`short_supply_donor_deletion` も任意の正周期pを扱うが、全 `U` メンバーが範囲内current-Aで、
最小P2のlag 3/7/11に限られる。任意の `B.Sublist U` についてdonorの真の最古Sを削除した後もHallを保つ。
Uの完全性、donorのU所属、正drift、実軌道は仮定しない。従って「完全な全lag供給集合からの削除」ではなく、
短い要素だけからなるUに限った直接系である。証明は短窓Hall、E-360 Q、既存のtight/slack削除補題の
合成であり、非空・実削除例を持つ意味のある `PROVED-LEAN` 系ではあるが、新しい数学的入力でも新規E行でもない。

意味監査では、p8/p11の非空・実削除例、空B、周期境界、E-240の非AAS緊密集合、E-069/E-133の
最古S単射反例を照合した。SS=2を外すとp12 `AAAASAAASSSS`, `B=[2,5,7]` で失敗する。
また7 donorの真の最古offsetは10または11であり、固定offset11への置換は不可である。
使用済みp32/33標本は有限証拠にすぎず、全体の独立認証も未完了で、Lean証明の代用にしない。

以上から、今週言えるのは「一般p・短lagにおけるQと、そのall-short Uに限る削除系」までである。
一般lag、lag 15以上を含む緊密集合、一般Gate T6、完全all-lag U、E-070/E-067、実Recaman軌道、
全射性は未解決。昼の形式化前独立入口検査欠落と初回checker保存欠落も履歴として残す。
公式G5冒頭の `application pending` は適用前時点の履歴文であり、実適用と適用後PASSの正本は
`docs/adversarial_audits/H-20260920-01_20260921_0200.md` の最終節である。旧文言は遡及改変しない。
この週は範囲を延長せず、次の計画では一般lagへの独立した橋を新しい一問として入口監査から始める。

## 後半候補・反例・停止の監査済み範囲

対象版と合同判定は [01:30合同監査](adversarial_audits/H-20260920-02_20260924_0130.md)、
凍結元文・逐語signature・根拠対応は
[01:30 packet](data/issue73_20260924/slot0130/candidate_packet.md) を参照。

後半候補は、限定意味監査の合格と総合研究手続きの合格を分けて記録する必要がある。
H-20260920-02、H-20260920-03、H-20260920-05はいずれも、対象を限定した独立監査で
statementと証明・例の対応が合格した部分を持つ。しかし三者とも昼の形式化前に必須だった独立入口検査が
欠け、後日の意味監査で遡及的に埋められない。カードは `CONJECTURED`、総合判定は**未完了**であり、
新規登録・昇格・確立済みの後続依存への採用は行わない。

H-02で限定合格した `short_tight_avoids_ss2_window` は、任意の正周期 `p` と周期符号語 `e`、
nodup・範囲内current-Aの緊密 `B`、各メンバーが最小P2のlag 3/7/11、任意の整数donor時計 `u0`、
長さ11 P2・SS=2 donorを量化する。donor最小性、donor current-A、ambient Hall、正driftは不要だが、
一般lag・lag 15以上・完全all-lag U・実Recaman軌道には届かない。p13
`AASSSAAAASSSS`, `u0=10`, `B=[7]` はnonminimal/current-S donorと非空tight Bの共存例で、
真offset11・phase12は回避される。これは非空性の確認であって、全周期の証明や新holdoutではない。

H-03で限定合格した `tight_neighborhood_eq_of_p2_prefix` は、`m<=lag<=11`、m側P2、lag側tightから
`N_m(B)=N_lag(B)` を結論する。Lean文はfull-lag P2もmの最小性も仮定せず、元カードより広い。
元カードからLean文への向きは確認されたが、逆向きは成り立たない。元カードのstrict/full-P2/tight領域は
既知p1..12とp15で0件であり、globalな不存在でも等式の反例でもない。p4 `AAAS` のlag4例は
full-P2でなく、p9 `ASAAASASS` のlag7例はtightでない。従ってstrict prefix reductionを
行使済みの新入力と記載しない。

H-05で限定合格したのは `moment_ending_A_budget`、`moment_ending_AA_ss2`、
`ss2_intervening_prefix` の局所3宣言だけである。最後は任意有限語 `w` について、A-endedな
`X=w++[A]` がmass 0、`moment(X)+|X|<=0`、SS数2以下ならstrictなS-ended P2 prefixを持つ。
非空例は `AASASASASSSA`、一仮定ずつ落とす負対照は `AAASSS`、`SASASSSA`、`SA`、
`AAASSSSA`。一方、後半Lean、紙§3-5、AAS/w1各配置、true-oldest分解との結合、周期lift、
任意長donor回避・削除は未監査で、H-05全体の最終定理もない。

H-20260920-04については範囲の異なる確定的な負結果がある。p16周期語
`SAAASSSASASASAAA`、`u0=15`、`B=[3]` ではdonor窓 `AASASASASSSAAAS` がP2・SS=2、
proper P2 prefix 3、真oldest offset15・phase0で、`N(B)=[0]`。従って真oldest回避と削除後Hallが失敗する。
この監査済みliteralは**非最小lag15 donorへの延長だけ**を `REFUTED` とし、その同一ルートを
`STOPPED` とする。最小lag15、任意lag、一般Gate T6、実軌道、旧census、第二w1例、最小p/lagは
決めない。固定offset11はphase4で、真oldestの代用ではない。

共通の境界として、E-240は純AAS forcing、E-069は最古Sの大域単射を退ける。E-345はSS>=3対照、
E-351はnext-A等を既に仮定するためWのnext-Aの証明に逆用しない。全メンバーshort-onlyという
制限付きUを完全all-lag供給集合へ、
有限周期語を実軌道へ、限定意味合格を総合合格へ読み替えない。p32/33や旧censusは既に使用済みまたは
独立再認証されておらず、新holdoutと呼ばない。

以上より、週間後半について監査済みとして記載できる範囲は「三つの限定意味監査結果」と
「H-04の非最小lag15に限る反例・停止」
までである。H-02/H-03/H-05は総合未完了のため `CONJECTURED` を維持する。新しい独立入力なしに
一般lagルートを延長しない。次に再開するなら、任意lagと実軌道を分離した新しいbounded cardを作り、
形式化前の独立入口監査を先に完了する。

## 週間の未監査一覧と探索終了判断（02:00）

以下は新しい数学的成果ではなく、週間計画に残った未完了を確立済み結果から分離する記録である。
対象版と独立判定は適用時に
[02:00監査](adversarial_audits/H-20260917-01_20260924_0200.md)と照合する。

確立済みの上限はE-360の一般p・short-lag Q/Wとall-short U削除系である。反証済みなのはH-04の
**非最小lag15 donorへの延長だけ**で、同じ限定ルートだけを`STOPPED`とする。最小lag15、一般lag、
一般Gate T6、実軌道は反証されていない。9/22の時間外未着手も数学的停止ではない。

9/20 01:30の壊れた反証ゲート実装枝は追加修理を停止済み。9/20 02:00のproper-U probeはw1前件0件で
未完了であり、第2修理・即時範囲拡大を禁止した。後日のp20別非空例を旧probeの成功扱いにしない。
これらの限定された実装/実験停止を、Q/Wや一般lag数学ルート全体の停止へ広げない。

未監査計算は、使用済みp32/33各2000語標本の全体独立認証、matching-closure lag19の4 shardの
revision・分割完全性・重複・生成条件、H-04旧32768/85/46 censusと第二w1例、H-05の任意長donor
census、H-02のfixed shortOff衝突3件である。いずれも旧ログまたは`OBSERVED`を越えて扱わない。
H-03のstrict/full-P2/tight領域は指定済み有限範囲で0件と独立再現済みだが、global不存在ではなく、
上限延長もしない。
また9/20初回`baseline_q_w.py 15`はexclusive-bound bugを含んだまま60秒SIGINT・exit130・stdout空で、
後のinclusive p1..11成功により遡及修復しない。p15の成功や有限分類に数えない。

Lean・紙上候補では、H-02は限定statement、H-03は近傍等式、H-05は紙§1-2に対応する局所3宣言だけが
限定意味監査済みである。H-02/H-03/H-05はいずれも昼の形式化前独立入口検査がなく総合未完了、
`CONJECTURED`を維持する。H-03のH-02依存downstream 2宣言は未監査。H-05は全13宣言中、残る10宣言、
紙§3-5・AAS/w1配置・true-oldest分解・周期OwnerFamily接続・任意長donor回避/削除も未監査である。
H-05全体の最終定理、公式G5、Auditへの対象直記はない。lint13/13を残る10宣言の意味合格としない。
失敗runのsource/hashや初回prehashの欠落は後日の再構成・再生で遡及修復しない。

残る数学的義務は、最小lag15 memberのtight Bからの排除または反例、任意offsetを扱う一般lag機構、
donorを含む部分集合の一般p削除後Hall、完全all-lag Uの容量、任意長donorの局所語から周期への接続、
周期符号語から実Recaman軌道への橋である。有限lag19、short-only U、G2だけからこれらを導かない。
E-070/E-067と全射性は未解決のまま。

従って今週は、限定新補題と限定反例という計画上の成果を保存して探索を延長せず終了することを推奨する。
これは時間・運用上の終了であり、一般lagルート全体への新しい`STOPPED`判定ではない。
02:00枠で決めるのは未監査一覧と探索を延長しない判断までであり、承認版もこの枠で保存する。
02:30の予約済み別最終枠には、週間最終保存の照合、全worker/process終了、予約終了の確認だけを残す。
今回の02:00担当をそこまで継続する意味でも、今回承認版の保存を先送りする意味でもない。従って既存冒頭の
「週間全体の最終停止・再開判断はまだ未完了」は02:00適用前の履歴として矛盾せず残す。

lag15 member排除は次の候補endpointだが、E-356の有限排除と見送り済み10,026-node証明書に隣接するため、
再実行・検査器改善・lag上限追加だけでは再開しない。現時点の再開条件は未充足である。
再開可否を決める最小の一問は、根S offset `k`、owner offset `kx`、true-oldest offset `r`、owner長`Lx`の
`delta=r-kx`とold A-tail座標を保持し、最小P2とM1/M2からlag上限非依存のfalsifiableなowner-offset制約を
一つ得られるか、である。具体的不等式・有限分類・単調量を凍結し、既知lag3/7例と弱化historyで
形式化前独立入口監査を通った場合だけ、lag15 endpointを新カードとして開始する。
このdelta問い自体は量化子・式未固定の将来カード前gateであり、承認済み新数学ではない。
## 週間最終終了記録（02:30）

02:00承認版を保存版として照合し、週間結論・未監査一覧・再開条件は変更しない。対象HEADは
`08c08565c743f39350c9b959e1df7d30aa1cae5d`。02:30開始時の親manifestは25/25 OKで、週報・主カード・
handoffのSHA-256はそれぞれ `00b149ea96eafdddcbfbe4a4e09031ca0779ab1ffdfd93fa941d02bb57dfd9d2`、
`7f73cc1ec105e699b571e5f0df78d5ddcef670dc304f44a9d5df9efee078b479`、
`1846cf280c8f911a5e5358f6ef24e23134dd4b7cd3b68bae3cedf245c939d13c` と一致した。

したがって週間の数学的上限は、E-360の一般p・short-lag Q/Wとall-short U削除系の限定
`PROVED-LEAN`、およびH-04の非最小lag15 donor延長だけの `REFUTED`・同限定ルートの
`STOPPED` のままである。WはOwnerFamilyの4フィールドを仮定し、E-351の既存next-A仮定へ循環
させない。H-02/H-03/H-05は `CONJECTURED`・総合未完了で、H-03 downstream 2本、H-05の
残る10宣言・紙§3-5・周期接続、p32/33標本、lag19 shards、旧censusは未監査のまま残る。
完全all-lag U、一般Gate T6、最小lag15、一般lag、実軌道、E-070/E-067、全射性へは進んでいない。

根拠の逐語signature・定義・原ログは [01:00 packet](data/issue73_20260924/slot0100/candidate_packet.md)、
[01:00逐語監査](data/issue73_20260924/slot0100/verbatim_statement_audit.md)、
[01:30 packet](data/issue73_20260924/slot0130/candidate_packet.md)、
[02:00 packet](data/issue73_20260924/slot0200/candidate_packet.md) と各
[01:00監査](adversarial_audits/H-20260917-01_20260924_0100.md)、
[01:30監査](adversarial_audits/H-20260920-02_20260924_0130.md)、
[02:00監査](adversarial_audits/H-20260917-01_20260924_0200.md) に固定する。
今枠では新しい数学、探索、Lean、vacuity/lint/check、登録・昇格、未監査10宣言の認証を行っていない。

今週の探索を延長せず運用上終了するが、これは一般lagルート全体への数学的 `STOPPED` ではない。
再開条件も未充足であり、`delta=r-kx` とold A-tail座標を保持する案は量化子・式・全仮定・非空例を
固定した新カードを別Solが入口監査するまで将来card前gateに留める。旧OS、純AAS、lag15力任せLean、
単なる上限追加は再開しない。02:30候補は別Solの独立合格前には未完了である。親は02:33:23 JSTに
automation `recam-n-1-3` を `PAUSED` へ更新し再読確認した。status/updated_at以外は不変で、証跡は
`docs/adversarial_audits/H-20260917-01_20260924_0230_parent_files/AUTOMATION_STOP.json`
（SHA-256 `c96851c9079b6ba199c52fc836c303f6005d0a8b2bd5893524d08ef0f1bc2168`）。
全worker/processと親の終了は、各確認前に先取りしない。
