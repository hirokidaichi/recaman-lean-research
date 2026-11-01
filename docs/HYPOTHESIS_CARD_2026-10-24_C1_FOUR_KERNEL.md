# Hypothesis card: r4のA-event macro simulation

- ID: H-20261024-01
- Parent: E-388 / E-389、[2026-10-23 DAILY](RESEARCH_HANDOFF_2026-10-23_DAILY.md)
- Status: PROVED-LEAN（E-390の実語macroのみ。後続r4分類kernelの方法はSTOPPED、分類命題は未証明）
- Mode: C1活用。r≤3の深さ/Q、C2/Pの初期監査を反復しない。

## 一問・全量化子

任意f、任意padded BlockWord prefix終端n、その後の正不足prefix [n,b)、
全A数≤10、元0基点の非Endable A数≤4、任意のS-only gap長jと次のAを取る。
第11Aへの停止線以前という帰納段で、次状態を
「全A・非Endable A・S数min19・S<19なら全tail/それ以外は末尾19符号」で表す。
任意jの実際のA0/A1遷移が、j'=min(j,19)の有限macro edgeに**包含**されることを証明できるか。
old signatureは必要条件を独立に許す過大なモデルなので、実際のEndableとの同値を要求しない。

## chain・受入・停止

1. local P2長は先行A≤10から≤19。S≥19ならE-385がold supplyを排除。
2. j≥19の次AはE-389から必ず非Endable。非Endable Aは長いgap後にも置けるので切らない。
   次の符号列はS18 A、Sフラグ19、A/ANを一つ増やす。正不足はS≥19・先行A≤10から保たれる。
3. j≤18は実語全suffix/local/必要old signatureからmacro edgeへ移す。
4. 以後、A-event certificateにE-389のterminal S-rayを組み合わせてr4のkernel分類へ使う。
   全長A≤10を仮定して結論にせず、前状態のinvariantから供給して第11Aを排除する。

受入は上の全量化子のLean simulationと小例/境界/弱化反例、または失うclock情報の具体例。
最初の15分で新しいsimulation edgeを供給できなければ、定義だけを増やさず停止/切替する。
切替先はterminal wordの一般有限供給certificate（零追加free予算）を先に閉じる一問。
n=bの初期状態はE-378のS-run後に窓なしを別に使う。空prefixを漏らさない。

## 予定と実績

次回の予定は開始10・C1活用60・局所探索30・別pass監査10・引き継ぎ10。
探索CPU当初0。新しいgraph生成が必要なら上限/argv/source hash/discovery/独立holdoutを実行前固定する。
保存済みr4の計算結果を証明として仮定せず、kernelで検査する対象として使う。
停滞連続回数は前日から継承し、同じ無変化2 cycleなら40/50/10へ変更。日付でリセットしない。
実績は未実行。06:00の最初のtool内で時計/status/setup startを済ませ、その後に資料を読む。

## 実行前の具体化（2026-10-24）

親cycle R-20261024-01。最初はfull-S遷移の反復を`gap(s,j)`に集約する。
19回以上のSでwordはS^19、Sフラグ19となり、A/非供給A個数を保った同じ状態になる。
actual stateが`gap(member,j)`という表現を保つ帰納を予定する。
Sではjを一つ増やす。Aではmin(j,19)の有限edgeへ移す。
先行A≤10はmember invariantから供給し、全長A≤10を仮定しない。
終端不足1の語のチェックは全j=0..19を対象とし、初期S終端を含める。
小例/境界の反証を先に行い、macro soundnessの新edgeが15分で得られなければ切替。
CPU当初0。新しい探索が必要な時だけprotocolで予算・実装・独立holdoutを先に固定する。

## 最初のgate通過と事前CPU再配分

06:08前に、gapの任意長飽和・composition、実際のS/A更新・actualFourState_macroが
個別Lean検査を通過。定義だけでなく実語の全A0/A1を有限edgeへ移す新入力を供給したため継続。
未登録であり、full check/Audit/意味監査前にPROVED-LEANへ昇格しない。
次はA-event graphの全closureとendpoint分類。全長A≤10を仮定せず前memberから供給する。
CPU0→120秒、wall≤100秒を実行前protocol/RUNSへ固定。C1残り枠から最大2分を移す。
未知のr4分類はまだCOMPUTED。一般C1/任意rは未解決。

## 06:27 判定・切替

実語macro simulationの個別Lean検査は成功した。一方r4大規模証明書のkernel検証は未完了。
全表・関数block・Nat block・state/edge列分離を試したが、約11GiBまたは事前4GiB上限で自己PIDを停止。
計算分類をPROVED-LEANへ昇格せず、**大規模一括decideの方法をSTOPPED**。
再開は実測で資源を減らせるchecker/証明分割、または数学的に正当な小さいquotientが得られた時だけ。
時間追加・メモリ上限引上げだけでは再開しない。
未検証dataはdiagnostic .lean.txtへ保存し、利用Lean sourceには未供給なtable仮定を残さない。
次はH-20261024-03の任意語terminal有限判定、および16rootを明示した将来面積入力へ切替。
r4全分類/a_z≤4のQと一般C1は未解決のまま。

## 検証済み判定

PROVED-LEAN: E-390（macro接続のみ。r4分類kernelは未完了）。full checkとAuditの成功ログを当日packetへ保存。
親C1/Q全体とr4全分類は未解決、個々の条件を省略しない。

## 最終実績（closed journal）

<!-- DAILY_CARD_ACTUAL_START -->
このカードに属するresearch区間は **1560.949秒**。共通setup/監査/handoffは親cycleでのみ計上。
closed journal: `docs/data/daily_research/2026-10-24.json`、親全体confirmed_work_seconds=7178.944。
<!-- DAILY_CARD_ACTUAL_END -->
