# Hypothesis card: 小さい第一A-block三run族の実free下限をLeanへ

- ID: H-20261028-01
- Status: PROVED-LEAN (E-432 upgraded from paper; full scope retained)
- Parent cycle: R-20261028-01; prior inputs R-20261027-01/E431/E432（費用は親cycleへ二重加算しない）。全体cycle連続無変化0は新しい供給edgeによる更新で日付resetではない。r4同表枝はE412/E427で2回削減0/0、STOPPEDのまま。
- Mode: C1活用60分の最初15分gate。予定setup10/活用60/探索30/別pass audit10/handoff10分。CPU探索は0から。

## 一回の問いと全量化子

任意f:Nat→Bool、n,a,h,M,R:Nat、BlockWord w、実prefix seg f0n=w++A^a、1<=M<=3、R>=5。
B=h+M+3R+3、seg f n B=Sh AM S^(R+1) A^R S A^(R+1)。実freeは元0の `f i=true ∧ ¬EndN f0i`。
**cN free n B>=2R-2を、R/語長/old長に上限なしでLeanへ移せるか。** Int元p版も元Endableを保持する。zero/positive不足/target供給や新しいdefined Hypを入力にしない。
R>=5/1<=M<=3を落とさず、R/Mを有限probe上限へ切らない。

## 紙上chainと最弱edge

正本: [E432ノート](RESEARCH_NOTE_2026-10-27_C1_SOURCE_FAMILY.md)。二つの後続A-rayは、全local sourceをkey=-2で分類すると各i2のみ。oldは既存E411で各run高々1。第一runはE417で最初min(M,2)がfree。従って元count加法で1+(R-2)+(R-1)=2R-2。
最初15分のunitは**第三A-rayのlocal供給がi2だけになる全長source分類**。A-only途中start/5source型/全uとsame historyを保つ。閉じれば第二ray分類→old予算→実free count接着→Int元p→G5/Audit/lint/check。
E431の再利用式は共通uから最後A-rayとその後一つのgapへの二窓だけを扱う。任意混合futureの全source単射には拡張しない。

## falsifier

R4はS² A⁴ SのP2で第三ray i0が追加される。M4/R5はS A⁴ S⁶ A⁴のP2が第二ray i4を追加する。両仮定が必要。
h0、M1/2/3、endpoint S、old/local重複と複数start同clock、元p/半開count/target除外を監査する。
E430のM1/L5/T6/R5/d1/m6/s1/free(1,2,1)は弱化count反例で実EndN履歴ではない。head39実free10を数値4に置換しない。

## 受入・停止・切替

既存のsource予算を再包装しただけでは不受理。第三rayの全length source型の新しい排除edgeか、実free下限の接着を供給しG5/Audit/check後にだけPROVED-LEANへ。
15分で新edge/候補削減/反例なしなら本形式化unitはSTOPPED、残り45分を第二S起点targetの平方条件と実free coupling25分、old/初期S源の共通prefix十分条件20分へ移す。一日は終了しない。
数学修理は1回。E415の小定数修理、同r4表/同R19 spectrum/未検証R11 kernelの時間/メモリ追加は再開しない。
R19は3001state gate STOPPED。R7/R11有限kernelはOS AS1GiB拒否で未起動。Lean -M512を用いた別の小factor証明は検証済みだが、AS/tree全体capや同表再開の根拠ではない。
新CPUが必要ならsingle cooperative Python/子process禁止の契約を再確認し、費用/argv/源hash/discoveryと独立holdoutを実行前に固定する。既存graphはdiscovery。

## 引き継ぎ

[10/27 DAILY](RESEARCH_HANDOFF_2026-10-27_DAILY.md)と末尾の追加handoff、E432ノートを先に読む。E416全長reduction/E423有限実代表/E429source場所制約/E431再使用式は完了unitとして消費し、初期C2/Pやr3分類を再実行しない。
実績は当日journalの確認済み区間だけ。旧日/CPU/予定を加算せず、終了時に必ずstopと日本語日次finalを行う。

## 2026-10-28 result

PROVED-LEAN (E432 strength update, same claim as paper). Third-ray first gate passed06:02:28; full check06:06:24,428jobs/2924axiom declarations. Main `family_free_lower` and `family_free_lower_int` in `Recaman/SourceFamilyFreeCount.lean`, literal G5 E432. All h/R/old lengths quantified, M1..3/R>=5; zero/positive/target not assumed. Pointwise actual six run signs present the exact word shape. No mathematical conjecture repair; elaboration/count association corrections only. Actual times in today's journal; phase transitions not duplicated with parent costs.

Next H02 evaluates removing M<=3 using source divisibility; E432 is not rerun as another unit. General three-run/C1 still open.

<!-- journal actual -->
## 確認済み実績（親cycleと二重加算しない）

2026-10-28T06:01:36.691198+09:00–2026-10-28T06:07:55.253101+09:00、6分18.562秒（当unitのresearch/audit込み）。[journal](data/daily_research/2026-10-28.json)の確定区間のみ。親cycle全体は119分13.128秒、未終了区間は未計上。予定局所上限と実績は別。終了後の確定値はDAILY参照。
