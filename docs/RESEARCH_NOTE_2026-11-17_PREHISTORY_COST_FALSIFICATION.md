# 供給元の前史費用：反証探索と残った反例領域

後続の夜調査でM5/low free<=4も全深さ・全上昇幅で排除した（[E735紙上証明](RESEARCH_NOTE_2026-11-17_POST_RETURN_HIGH_FREE.md)、全体未Lean・人間レビュー未）。以下はこのノート作成時点の証拠と停止記録を保持する。

これは最初の調査の記録。後続の明示M4調査では、M4/low free<=3を任意深さで排除した（[E729紙上証明](RESEARCH_NOTE_2026-11-17_FOUR_PERIOD_SOURCE_ORDER.md)）。以下の失敗・停止・当時の結論は保存する。

結論：`M <= F_low(T)` の反例は得られなかった。一般命題は **CONJECTURED**。ただし紙上で **M<=3を全長で排除**し、**前史が初期Sの底より3段下までなら全Mで成立**することを確認した。従って本当に探すべき反例は、**M>=4、前史が初期Sの底より少なくとも4段下へ達する場合**に限られる。さらに同族source時計の間隔は12以上。これは全射性/C1の解決ではない。以下の新しい接続は **PROVED-PAPER、未Lean・人間レビュー未**（E-728）。

## 命題と元履歴

正本は[H-20261117-PC](HYPOTHESIS_CARD_2026-11-17_PREHISTORY_FREE_COST.md)。元0基点の±1歩行Hと累積面積Bを使い、

    Win(u,q) : u<q, H(q)=H(u)+1,
               B(q)-B(u)-(q-u)H(u)=0

とする。f(q)=Aで少なくとも一つの元Winがあるときだけactual supplied Aと呼ぶ。全sourceを保持する。

初期h>=1符号はS、T>=h、[T,T+8M)はZ^M（Z=ASSSSAAA）、最後T+8MもA。全てのplateau Aが元actualで、各境界T+8jのsource全体は{h-1}。全非空prefixの元supplied+1<=Sも仮定する。F_low(T)はq<T、元free A、H(q)<=1-hの個数。総freeとは区別する。

境界source条件からH(T)=2-h。各周offset5のtargetは高さ-1-h、そのsourceは **c=-2-h**。前史にあるM個のsourceはkey差24の別々の値を担う。offset6側はsource高さ-1-h、key差16。この2M個の必要sourceの導出は[前のノート](RESEARCH_NOTE_2026-11-17_PREHISTORY_COST_PIVOT.md)にある。

## 紙上補題1：M<=3には反例がない

より一般に、元履歴がS^hで始まり、あるu<TでH(u)<=-h-2、かつH(T)>=2-hなら、q<Tに高さ<=1-hの元free Aが少なくとも3個ある。全prefix正不足も、標準軌道到達性も、この補題には不要。

**最初の四つのAの監査。**

1. 最初の二つのAはfree。最初のA以前にはAがない。二番目以前にはAが一つだけなので、mass1を持つ窓は長さ1のAしかなく、面積1で供給にならない。両者の高さはそれぞれ<=-h、<=1-h。
2. 三番目のAが供給されるなら、strict pastのAは二つまで。mass1から窓長は1又は3で、供給できるのはSAAのみ。従って最初の三つのAは連続する。
3. 三番目がfreeなら、その高さは<=1-h。これに反して高さ>1-hなら、前のS数はちょうどhで、S^hの直後の連続三Aとなり、三番目にはSAA供給がある。
4. 三番目がactualなら四番目はfree。四番目以前にAは三つまでなので窓長は1/3/5のみ。Winの長さは3(mod4)だから3しか残らないが、連続した最初の三Aの後には、Sを挟んでも挟まなくてもSAA suffixを作れない。

**深い訪問からの帰還。** F_low(T)<=2と仮定する。uからTへの上昇だけでAが少なくとも四つあるので、最初の四つのAは全てTより前。最初の二つがlow freeを使い切るため、三番目はactual、四番目はfreeかつ高さ>1-hでなければならない。四番目の直前S数はh+1以下。従ってそれ以前の全高さは-h-1以上である。

一方、[0,T]の最小高さmは-h-2以下。H(T)>mなので、最小高さを最後に取る時計v<Tでf(v)=Aとなる。vは四番目のAより後である。vの供給には過去の高さm-1が必要だが、これは全prefix最小性に反する。従ってvは元freeであり、高さm<=1-hの三個目となって矛盾する。

plateauがM>=1周あるなら、offset5のsourceがu<T、H(u)=-h-2を内部に供給する。よって **F_low(T)>=3**。M0は自明なので、目的の不等式はM<=3の全域で成り立つ。

**弱化モデルでの境界。** h2、前史S4A4は最低-4からH(8)=0へ戻り、low freeは時計4/5/7のちょうど3個。この高さ回復補題だけで4を主張できない。T8をAへ補完しても元source1のWin面積は-8であり、plateauの親domainには入らない。これは親予想の反例ではない。

## 紙上補題2：前史の床が-h-3以上なら全Mで成立

追加仮定は `forall k<=T, H(k)>=-h-3`。上方のexcursion、前史長、run数、Mは無制限。c=-h-2と置く。最初のsource族の各元時計uはH(u)=cであり、相異なるM時計を得る。

各uを、f(u)=Aならu、f(u)=Sならu+1へ送る。

- Aの場合、時計uの高さは床+1。供給sourceの高さは床でなければならないが、そこからuまでの相対面積は非負で、終端の高さ差1により正。従って元actualではなくfree。
- Sの場合、次の高さは床。H(T)>cなのでu+1<Tであり、もう一度Sを置くと床を破るためf(u+1)=A。このAには床より下のsourceがなくfree。
- 像はいずれもTより前、高さ<=c<=1-h。異なるsource時計の像は交わらない。衝突すると二sourceは隣接する必要があるが、±1歩行の隣接時計は同じ高さcを持てない。

よって元low freeへの負荷1の単射を得て、**M<=F_low(T)**。これは元sourceを変更せず、元0基点のfreeを使っている。

この接続に必要な「床と床+1のAは元free」は既存Lean定理 `Recaman.BlockSuffixPositivity.block_prefix_low_clock_not_endable` のn0/空BlockWordの場合。別経路では `Recaman.FloorSupplyFreeBudget.actual_floor_supply_count` をplateauのoffset5（床+2）へ適用できる。既存床原理の再発見を新しい深さ一般原理と数えない。新しく明らかになったのは、今回の費用予想と反証生成器の適用域がこの既知原理に含まれていた点である。

従って親反例には **あるk<TでH(k)<=-h-4** が必要。最初のunit-loop生成器と既知E715の固定深さ5/initialS2族は、この反例領域へ入れない。

## 紙上補題3：同族sourceは12時計以上離れる

高さcへ戻る長さLの橋を考える。L=2rは偶数で、相対面積Aは `|A|<=r^2`。各中間高さの絶対値をmin(i,L-i)で抑えて足せばよい。またAの偶奇はrの偶奇に等しい。

第一族の異なる二source間では、相対面積は非零の24の倍数。従ってrは偶数で、r^2>=24。ゆえにr>=6、**L>=12かつL=0(mod4)**。第二族の16の倍数には同様にL>=8。

M個の第一族sourceを時計順に並べると、順番がtargetの順番と逆でも隣接間隔は12以上。最初のsourceは高さ-h-2へ到達するためh+2以後、最後はTより前なのでT>=h+12M-9。さらに元境界Winの長さT-h+1は3(mod4)、すなわちT-h=2(mod4)。合わせて **T>=h+12M-6 (M>=1)**。

長さ12・面積24はA4S3A2S3、長さ8・面積16はA4S4で達成可能。面積の上限だけで長さ10を許してしまわず、偶奇を使う。時計間隔をfree間隔と読み替えてはならない。

## 反証実験の結果

初回生成器は二つのsource key列を、負の高さのAS/SA補間で同じ元前史へ埋め込んだ。discovery M3/4、holdout M5/7、全144候補順序のうち81個が長さ上限内で構成された。残り63個は上限超過で未評価。すべて親domainを満たし、反例なし。しかし全て床>=-h-3であり、補題2の対象だったため、この探索法を **STOPPED** とした。

深い構成は面積調整をS^k A^k（面積-k^2）へ変更した。旧生成器の範囲拡張ではなく、床の制限を外す別の構成である。discovery M4/5、holdout M6/8、96候補順序中94個を構成、2個は長さ上限超過。得られた最小費用は以下。これは生成した履歴内の最小値で、全履歴の最適値ではない。

| M | 最小low free | 前史T | 初期S長h | 初期Sの底からの追加深さ |
|---:|---:|---:|---:|---:|
| 4 | 44 | 168 | 22 | 6 |
| 5 | 51 | 194 | 24 | 6 |
| 6 | 61 | 241 | 27 | 6 |
| 8 | 89 | 309 | 31 | 6 |

各最良証人の全Aに対する全sourceを、逆向きliteral mass/weighted-area走査で独立に再計算した。親domain、low freeの全時計、free総数、offset5/6の外部供給元表が一致した。他のAのsource表は発見時の出力に保存していないため、全Aのsource表同士を比較したという主張ではない。反例は得られず、費用は境界M-1よりかなり大きい。このため深い構成の有限探索も **STOPPED**。有限不在を一般予想の強い支持や次の範囲拡張の根拠にしない。

別の制約モデルは前史の各符号を未知数とし、全元EndN同値、全prefix正不足、全境界の唯一source、plateau全actual、F_low<=M-1を同時に入力した。既知E711を固定したbudget12/11のSAT/UNSAT対照は通過。未固定の(h,T,M)=(2,40,3),(2,56,3),(3,65,4)はいずれもsolver resource limitで **unknown**。反例不存在とは数えない。各instance/この方法は **STOPPED**、同じmodelを資源だけ増やして再実行しない。後でM3を排除できた根拠は補題1の紙上議論であり、solverの出力ではない。

## 検証・失敗・証拠の限界

- 全数学スクリプトのargv、source/dependency hashes、事前protocol、生出力、wait4のCPU/wall receiptは[data packet](data/prehistory_cost_20261117/PROTOCOL.json)以下に保存。実行はcooperative single Python process契約で、汎用process-tree sandboxではない。
- 発見/holdoutのMとseedを先に固定したが、同じ構成族なので統計的独立性は主張しない。小さなprefix空間は既知と重なるためfresh holdoutと呼ばない。
- first-four-A/global-minimum補題は長さ12の全2048開始S語、h1..4/T<=12で該当530件を有限反証検査し違反0。一般的根拠は上の紙上証明。
- deep audit初回は__file__未設定で、数学的検査前に失敗。失敗版/出力を保持し、検証計画の一度だけの技術修理を明記したR1は同じ入力・数学・資源上限で合格。黙って失敗を成功へ置き換えていない。
- Leanは変更・実行していない。E728はPROVED-PAPERのみ。全般のlow-free費用は未証明。新しいcountermodelも得ていない。

## 判断と次の一問

親予想は **CONJECTURED**。今回の受入は、元の反例候補をM>=4/追加深さ>=4/source間隔>=12へ削減した紙上接続。`local_progress`はM<=3と床条件付き全Mの排除、`depth_general_progress`は未達。時計の一様下限にはfreeへの未払いが残り、固定した浅い床の成功を深さ一般の成功と数えない。予定の日次parent cycleやtrackerをresetしない。

次は **M4/F_low<=3、前史の上方excursion無制限、最低高さ<=-h-4** に対し、三つ目の元low freeの前後で四つの24j+15 keyを同じ履歴へ置けるか、紙上でsource順序を絞る。受入は新しい元source/freeの必要条件又は正確な親反例。15分で変わらなければその順位法を止める。深い生成器のorder数、M、長さやsolver resource limitを増やすだけでは再開しない。M4を閉じても全Mの進展とは別に評価する。

既存 `RankThreeEarlyFree.rank_three_slack_at_five` と `RankThreeForwardClock.rank_three_forward_clock_band` は元区間の**全free<=3**を仮定する。今回のlow free<=3からは適用できない。高い位置のfreeを消したり、global minimumの後へ元基点を取り直してBlockWordを仮定したりする接続は未証明のまま。二free回復定理も、既に数えたlow freeとの重複を自動的には除かない。

## Handoff

変更はPCカード、本ノート、E728台帳/索引同期、再現packet。前の相談のMCカード・PIVOTノート・packetも同じchat所有として保存する。既存11/07 journalは他session所有で除外。最強の証拠は補題1/2/3の紙上argumentと、元全sourceに関する独立有限照合。一般の不足はfree3を超える深い前史の償却。実験の無反例・unknown・技術失敗は上に区別して残した。公開/検証結果は別receiptへ記録し、研究時間へ加算しない。
