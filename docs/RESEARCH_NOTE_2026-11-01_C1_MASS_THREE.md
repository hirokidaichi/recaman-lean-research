# 2026-11-01 C1: mass3 targetとoldmass4-clock0の実free課金

最終更新: E484はPROVED-LEANへ更新。E498の独立same-target平方比較/E497 headfree5により元p全gapを供給し、最終S local band仮定も不要。以下の早朝PAPER/四SB chainは履歴であり、現在のkernel証明はMassThreeOldZeroGap/Baseを正本とする。旧scalar layout STOPPEDは解除しない。

## 結論と正確な範囲

H-20261101-01の部分枝は次の紙上chainでfull-tail free-gapを得る。
現時点では **PROVED-PAPER（未Lean・人間レビュー未）**。新しいLean結果ではない。
四run全体、他のtarget/source位置、nonzero-mass、任意run数のrank、Q/C1/H/SL/全射性は未解決。
個別Lean layoutは512MBで初回と一回修理とも失敗し、未検証sourceはpacketへ隔離した。

正本の全量化子は[当日カード](HYPOTHESIS_CARD_2026-11-01_MASS_THREE_ACTUAL_CHARGE.md)。
任意の元Int p、任意のpadded BlockWord prefix、元nでzero、n以後全positive deficit、
正三A-run head

`z = S^h A^M S^m A^L S^s A^U`, `S=h+m+s=M+L+U`, `H=2S`,

と、その後の `S^3 A^T S^j` を考える。全h,M,m,L,s,Uは正、全長に上限なし。
同じ元prefixのold target suffix yのmassが3、同じprefixの別suffix xのmassが4で、
xが最後A-rayのclock0を実P2供給する。yは最後gap後のtargetを実P2供給し、
最後S3の内部にfinal-bandのlocal sourceもある。結論は元pの真のEndableによる

`R=j+1 <= actual_free(n, H+3+T)`。

target/source以前のprefixや、その他の高mass old sourceを切らない。
元pからNat0への添字移動は既存のEndable/EndN count移送とcN加法だけを用いる。
padded prefixも`block_append`/`block_replicate_A`により同じBlockWordとして保持する。
標準Recamán軌道での到達可能性は主張しない。

## 使う既存のkernel入力

- `actual_target_word_profile` / `actual_zero_mass_target_key`: 同じtarget窓の語・mass・area・key。
- `actual_old_window_root`: 同じold supplier窓の実prefix suffixとkey。
- `actual_final_S_source_A_budget`: final-band源とold targetから全A>=2R+2。
- `positive_r3_additions_free_bound`: actual free<=3なら全A<=2free+1。
- `four_run_supply_le_seventeen`: 同じpositive履歴の全実供給<=17。
- `three_run_count_of_manyS`: headの全実供給<=10。
- `single_A_run_free_budget`: 最初A-runのM<=実free(first A)+2。
- `three_head_moment`: B=S²-2I、I=M(m+s)+Ls。
- `zero_mass_area_parity`: B≡S (mod2)。
- `block_mass_three` / `block_mass_four`: area3∈{5,6,7}、area4∈{9,10,11,12,13}。
- `local_fourth_sources`: 最後rayの全local源を初期S/第一A/第二S/第二A/第三S/clock2へ分解。
- `sourceAt_count_le_one`: 同じ定符号runからの供給clockは高々1。
- `first_A_clock_equation`、`tail_S_small_gap_clock`、`tailOldRay_clock_unique`。

これらはE483の未Lean五area対や停止したr4/133core表、未Lean E384存在方向に依存しない。

## 紙上証明

### 1. 元actual counterが供給する上限

Fをhead+最後separator+最後A全体の実free数とし、F<Rと仮定する。
targetのmass保存から `3+0-3+T-j=1`、従って **T=R**。
もしF<=3なら既存r3により全A<=2F+1<2R+2で、同じfinal-band/targetのA下限と矛盾。
従ってF>=4、R>=5。全AはS+T=S+R。実供給をEとすると
`F=S+R-E`、既存E<=17とF<Rから **S<=16**。
これらは全て元actual counterからの出力で、入力仮定ではない。

### 2. 同じ二窓の原始key

a4=areaW x、a3=areaW y、B=-areaW zと置く。Bへの帯条件は置かない。
`runKey x=2a4-20`, `runKey y=2a3-12`, `runKey z=-2B`。
clock0の同じ実窓のkey=-2から

`2a4-20-2B+16(S+3)-18=-2`, 従って **B=8S+a4+6**。

targetの同じkey=-2R²から

`2a3-12-2B+12(S+3)-18=-2R²`, 従って **R²=2S+3+a4-a3**。

a4=9..13、a3=5..7なので `2S+5<=R²<=2S+11`。
S<=16によりR<=6。R=5ならS<=10。
正三runなのでI=M(m+s)+Ls>=3、従ってB<=S²-6。
S<=10かつS>=0では `(S-10)(S+2)<=0` よりS²-8S<=20。
ゆえにB<=8S+14。一方B=8S+a4+6>=8S+15で矛盾。
従って **R=T=6、13<=S<=15**。

zero-mass語のB≡SとB=8S+a4+6からa4≡S (mod2)。
36=2S+3+a4-a3とarea各選択を同時に満たすのは次の四組だけ。

| S | a4 | a3 | B |
|---:|---:|---:|---:|
| 13 | 13 | 6 | 123 |
| 14 | 10 | 5 | 128 |
| 14 | 12 | 7 | 130 |
| 15 | 9 | 6 | 135 |

これはE483の五pairを仮定した結論ではない。actual供給上界と正三runのI>=3を先に結合し、
全長のactual counterを四数値組へ縮めた。元old語や高mass sourceを四状態に商していない。

### 3. 最初A-runへの実free課金

F<=5。最初A-runの実freeはfull-tail F以下なので、既存single_A_run_free_budgetから
**M<=F+2<=7**。原基点の同じEndNで評価し、headfreeや結論を仮定していない。

### 4. 初期S源の全長排除

headの初期Sからd個を除いたsuffixが最後rayのclock iを供給したとする。
massからd+i=4、従って0<=d<=4。keyを同じheadのmomentへ戻すと

`B=2d(S+3)-d²-8`。

d=0,1,2,3,4を代入するとB-8Sは順に
`-8S-8`, `-6S-3`, `-4S`, `1-2S`, `0`。
S>=13より全て非正。しかしB=8S+a4+6>8Sなので矛盾。
したがって初期Sからのlocal供給は全clockでない。

### 5. 第一A源はcounter域でclock0/2へ合流

同じheadのfirst_A_clock_equationをv=3へ適用する。
第一Aに始まる実local源のclock i<6は

`B-h²+8=2(4-i)(S-h+3)`

を満たす。平方へ直すと

`(h-(4-i))²=B-8S+2iS+i²-2i`。

i=0,2は残す。i=1では右辺が44/43/45/44で平方でない。
i=4では131/136/138/143、i=5では164/171/173/180で平方でない。
i=3では100/103/105/108。100以外は平方でない。
残るS13/B123/i3ではh>=1より(h-1)²=100からh=11、m=s=1。
momentは169-2(2M+L)=123、即ち2M+L=23。
M+L+U=13、U>=1から2M+L<=M+12<=19（M<=7）で矛盾。
従ってactual counter域のfirst-A源はclock0/2だけ。

**このM<=7を外した強化は偽**。下記のliteral discovery履歴ではh=M=11の同じsourceがclock3を供給する。
それでもfullfree15であり、親free-gapの反例ではない。

### 6. 全old/localを重複なしに数える

同じBlockWordとhead S3の全S数>=3から、old供給clockは`tailOldRay_clock_unique`により高々一つ。
仮定のoldmass4実窓がclock0を供給するので、**全massのold源はclock0へ合流**。
高massの他old源を切り捨てたのではなく、同じprefixの一意clock定理で含めている。

全local源は既存のexact六方向分類で含まれる。

- 初期S: 上の手順で不可能。
- 第一A: 上の手順で0/2へ。
- 第三S: 既存v<=3の平方補題で0/2へ。
- 第三A/最終S: 既存局所分解でclock2へ。
- 第二S: sourceAt_count_le_oneにより高々一clock。
- 第二A: 同じく高々一clock。

従って最後Aの全実供給clock集合は `{0,2} ∪ C_secondS ∪ C_secondA` に含まれ、
**実供給<=2+1+1=4**。同clockが複数の源から供給されても一度だけ数える。

### 7. 実headfreeと元full-tailへの接着

head全A=S>=13。もしhead実free<=3なら、同じheadまでのpositive条件と既存r3から
S<=2*3+1=7で矛盾。よって **head実free>=4**。
最後S3はAでないのでfree0。最後A6の実freeは6-実供給>=2。
cN加法とA=EndN+freeの恒等式により

`full-tail free = headfree + lastfree >=4+2=6=R`。

仮counterに矛盾。これでカードの元0/p/padded/zero-fullpositive枝の全長結論を得る。
証明の中で使うS上限/R6/四tuple/M7/headfree4/last供給4は全て内部導出であり、
未証明Propやfree結論を入力していない。元p移送は最初に述べた既存count同値で完了する。

## 反証passと実在性

実行前に2 CPU秒（discovery1/独立holdout1、wall各3秒）を固定。
cooperative single Python/nochildren/全thread累積CPU契約をfork拒否・wall停止・二threadCPU停止で再確認。
一般process-tree CPU上限の解決とは呼ばない。各workerのrevision/argv/source hash/dirty hash/出力は
[packet](data/mass_three_20261101/)に保存。

1. Discovery: old `AASAAA`、head `(h,M,m,L,s,U)=(11,11,1,1,1,1)`、S13/B123、v3/T6/j5。
   元0zero、全positive最小1、target源3、oldclock0源0、local q1/clock2。
   headfree12/fullfree15、last供給0/2/3。強いfirstA全域0/2にはclock3反例。
2. 独立holdout: old `SAAAAA`、head `(10,6,2,5,3,4)`、S15/B135、v3/T6/j5。
   元0zero、全positive最小1、target源3、oldclock0源0、local q1/clock2。
   headfree11/fullfree15、last供給0/2。

二つは **COMPUTEDの有限適用例**。全長証明の根拠、有限域の反例不在、標準軌道到達可能性ではない。
E480のold供給実在例と整合し、oldを消去していない。
area独立・自由Endable tagだけの弱化historyでは元count連結を供給できず、この証明の入力にしない。

## 形式化の失敗と未検証範囲

新しいMassThreeCounterNumbers layoutは512MBで最初の小area lemmaからkernel memory失敗。
不要なlower-band importを除く一回修理でも同じ失敗。source二版をpacket .lean.txtへ隔離し、
Recaman root/Auditへ入れていない。上限なし通常buildで採用しない。
既存MomentSmallHeadPruningの現sourceは同じ512MBで診断PASSしたため、
「Lean全体が使えない」や「既存証明が失効した」とは解釈しない。
同layoutへの資源追加/compiled import移動は再開理由でない。独立した数学的pruningか小certificateが必要。

紙上chainのLean実装、逐語statement audit、人間レビューは残る。
この文書のPROVED-PAPERをPROVED-LEANやC1全体の証明へ昇格しない。
