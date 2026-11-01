# Hypothesis card: 次の供給AまでのS-gap上限

- ID: H-20261023-05 / cycle R-20261023-01（局所探索枠内）
- Status: PROVED-LEAN（E-389）
- Frozen: 2026-10-23 07:16 JST、紙上提案・反証の前。

## 一問・全量化子

任意のf:Nat→Bool、padded BlockWord prefix [0,n)、n<b、j≥0を取る。
[b,b+j)が全てSで、元0からclock b+jが実際にEndableなら、

`j ≤ 2 * ones(seg f n (b−n)) − 2`（Intの不等式）

が成り立つか。右辺のAはgap前の**全A**であり、非Endable A予算ではない。
固定の全A上限・深さ・語長・H/Qは仮定しない。

## 役割・chain・反証・受入・停止

- 提案: old startならE-385で全tailのS≤2A−2、local startならmass1からj+1≤gap前のA。
  gap内startは全Sなのでmass1にならない。この三分が最弱の未知edge。
- 反証: j0、A0、n0、β空、SAAのlocal窓、SAAA|SSSSAAAのold窓を攻撃。
  BlockWordを外したSSAAA|A Sはj1/A1で偽。S-gapを外したSA|Aもj1/A1で偽。
  自由Endable tagには任意の長いgapを捏造できるので、実際のP2を必ず使う。
- 受入: 全量化子の紙上chainとLean証明、または全仮定付き実反例。
- 停止: 15分または07:32の局所探索終了。定義だけ/同値wrapperなら停止し、親の一般rankは未解決に残す。
- 用途: Aが増えるeventだけのcertificateへ圧縮するための有限gap判定。
  この補題だけで任意rのA上限や一般Qを解決したとしない。

追加CPU探索予算0。既知語の境界・弱化反例は既存直接ledger/紙上で照合し、Lean変更時は全checkとAuditを実行する。

## 実行結果

全量化子のLean証明と別pass監査を保存。最終checkは406 jobs/2743宣言、許可3公理内。
terminal wordはAASAAA/ASAAA/SAAASAAA/SSAAAASAAAの4prefixで実際の全P2 ledgerを確認。
子unitのCPU/形式化を親journalのH-20261023-05区間に含め、別時間として加算しない。
次はr4 A-event macro simulationで、このgap上限を供給Aだけに適用する。
