# H-20261103-01: short-target の実last供給と五band包含

Status: PROVED-LEAN（E523で最初のstrict候補削減を受入。E521五band全包含は次H02で引き継ぐ）。親R-20261102-01/H12。入口は11/02 DAILY→C1_NO_OLD note→SHORT_TARGET_BAND note→本カード。完了したC3全v/E515、C>=4/v>=CのE516〜518、E519 strict A cut、E520 source pruningを再実行しない。

## Exact question and quantifiers

E520 short_source_intの任意元Intp/padded BlockWord/元zero-fullpositive/全正三run zero-mass head、同old target実mass C>=4、1<=v<C、full-tail actual free<R=j+1という実counterをそのまま入力する。全六head長/全C/v/T/j/全old prefix/historyを量化する。D=C-v。実last Endable countのD1<=4/D>=2<=3はE522で完了した。第一の問いは、同じ元pの実countからS<=14/D+12を供給し、factored-circleでD1のC<=5又はD>=2のv<=3というstrict候補削減を内部供給できるか。元0 coreから元pへshiftする際も同じold target/sourceを保持する。

E520はR>=5/M<=R+1/old全排除と全initialS/firstA源の排除、middleS源ならD1/i0/M=R+1を供給する。第二A・第三Sは各1clock、第三A/最終Sは共有clock2。これらから実Endable全sourceを網羅する。未Leanのlast予算やfree結論を新Propへ仮定化しない。

## Acceptance and first gate

開始確認後の最初15分で、actual S上界とX=S-Cを保持したcircle比較からD1のC<=5又はD>=2のv<=3という新kernel候補削減を得る。E522の供給数は再証明しない。個別Leanは-M512/10CPU per-process/20wallを明示し、G5/Audit/fullcheckへ接続。紙上式のwrapper、予算を入力するadapter、有限head数だけでは受入しない。

E522と既存head supply<=10を元p actual partitionで結合し、S<=14（D1）又はS<=D+12（D>=2）を供給。同target keyからR²<=S²-2CS+v²-2Cv+1、S>2Cを先に供給した上で上界代入し、E521の五bandへ。

五bandは(v,C,R)=(3,4,5..8)/(4,5,5)/(1,4..8,5..9)/(2,4..7,5..8)/(3,5,5..6)。後三bandはR²+D²+4Dv+v²+24v<=145も保持。全C<=8/v<=4/R<=9/headS<=19/A<=21は出力であり入力しない。全old historyは無限で、有限history全分類/反例不在/C1ではない。

## Falsifier and stop

D1のmiddleS/i0を切らず、clock重複を供給数へ過大計上しない。Aをfreeへ置換しない。既知E453 mass1は適用外。source以前のprefix/他oldmassを切らない。S二次式の上界代入はS>2Cを先に証明する。

最初15分でedgeなしなら残45分を、D1の(C,v,R)=(4,3,5..8)/(5,4,5)におけるmiddleS/i0/M=R+1と後続free0の両立監査25分、same-target source平方/word parityの別機構20分へ再配分。数学修理は一回。旧表/H06/五tuple layout/同UNKNOWNへ時間・メモリ追加しない。CPU探索初期0、使用時は契約/上限/argv/hash/discovery/holdoutを先に固定する。

一般四run、C<=2、非zerohead、他target source位置、任意run/rank/C1/Q/H/SL/全射性は未解決。E521はPROVED-PAPER（五band包含未Lean・人間レビュー未、actual lastはE522でLean済み）から始め、未検証候補を昇格させない。

11/02追加停止: ShortBandArithmetic/ShortTargetBandsのmonolithic kernelは512MBでSTOPPED・未検証source隔離。単なるcast修正/分割/import移動や資源追加を再開条件としない。独立factor入力は X=S-C>0、D>=2でX<=12-v、同targetからR²+C²+2Cv-v²-1<=X²。actual S上界とこの比較を結合してstrict候補削減を先に得る。circleの同値wrapperだけは進捗にしない。

## 公開状態の開始確認

11/02の数学snapshot c8fb8b4cec79272045c26a0191a158f1c784e74fはorigin/mainへ到達・SHA照合済み。hosted CI 41358899803は07:54:58時点でLinux/macOS harness PASS、Lean/empiricalはcold certificate build中だった。終了journalを含む後続docs commitのSHAとpush結果は11/02最終chat報告を参照する。次回setupでorigin/mainをfetchし、その実SHAのCIを読み取り確認する。CI未完了をPASSにせず、失敗ならログと対象SHAを保存して必要な修正・通常pushへつなげる。ローカル622jobs/3364宣言PASSとhosted結果を区別し、CI待ちを数学探索CPU/実績へ加算しない。

## 11/03 開始前の役割・依存chain

R-20261103-01、CPU探索0。提案: actual partitionでhead10+last4/3からS+v<=C+13/12、同じtarget/headのkeyからX=S-C>0とcircleを供給。D1ではX<=14-C、deepではX<=12-vを非負積で二乗比較し、単調な下限でC<=5又はv<=3というstrict実候補削減へ。旧巨大Or算術jobのcast修理/分割を再実行しない。

反証pass（紙上、discovery/holdout該当なし）: C=v+1のmiddleS/i0を残す。S<=2Cでは負定数を持つtarget平方が不可能であり、S>2Cを先に供給。X上界を二乗する前にX>0と上界の非負を確認。D1C6の境界は25+2*36-2=95 > (14-6)^2=64、deep v4/C6は25+36+48-16-1=92 > (12-4)^2=64。C>=4/target/positive/actual counterのいずれも外して当該数値排除を全four-runへ適用しない。既知mass1/free-prefix反例E453は域外、Aをfreeへ置換しない。

形式化: 既存E522の同じEndN基点のlast上界を消費し、S boundは実countから供給。新unknown Propや供給予算/free結論の入力なし。factor helperだけでは受入せず、実phase/signの全長主定理に接着してからG5/Audit/fullcheck。別pass監査で元Intp/padded/zero/fullpositiveの量化子とwrapperの独立性を点検する。

06:05 gate候補: actual counts、factor helper、Nat actual strict cuts、元p/padded adapterが各-M512で成功。初回の結合正規化、未提供by_contra tactic、D1のgrind非正規化を、同じ数学statement/同上限で明示平方差identityへ変更。数学的仮説/量化子の修理なし、旧五band monolith未再開。G5/lint/Audit/fullcheckと別pass意味監査を通すまで受入確定しない。

06:06:18受入: E-523 PROVED-LEAN、fullcheck626jobs/3369宣言PASS、個別-M512/G5/Audit済み、人間レビュー未。actual countsと同target circleを内部供給して元pのS>2C、D1 C<=5/deep v<=3を全長で供給した。親cycleは継続しH02五band包含へ進む。数学CPU探索0、純helperの警告をdummy wrapperで消していない。
