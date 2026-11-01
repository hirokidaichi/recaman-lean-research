# Hypothesis card: 最高A10のprefixからの零追加free予算

- ID: H-20261023-06 / R-20261023-01（局所探索の残り、親と二重計上しない）
- Status: PROVED-LEAN（E-389）
- Frozen: 2026-10-23 07:21 JST。受入/停止を実装前に固定。

## 一問

任意f、padded BlockWord prefix終端n<n+|w|=b、
`seg f n (b−n)=w=S^5 A^3 S^4 A^4 S A^3`、任意K≥0について、
元0基点の非Endable A数が[b,b+K)で0なら、同区間の全A数も0か。

受入はfinite first-A certificate＋S-gap lemmaからの全KのLean証明と、
入力wを実際に供給するBlockWord prefixの全P2 ledger。
停止は07:32または未供給oracle/定義的否定への退化。先にA上限/深さ/語長を仮定しない。

## chainと反証

1. wは全A10なので、次のAがEndableなら前のS-gap j≤18（前カード）。
2. 全j=0..18でw S^jのlocal窓も必要old signatureもないことをkernelで確認。
3. future free A予算0から全future AはEndable。最初のAを仮定すれば1/2に矛盾。

これは有限のcomputable window検査であって、未知の「futureにAなし」を定義して仮定しない。
既存の実prefix探索がwに到達したがprefix名を保存しなかったため、mass≤4の13prefixを
独立直接ledgerで確認し、vacuousな初期条件を避ける。CPU5秒を当日の240秒内で事前固定。
future free予算を1に緩めて次のAを置く対照は結論を破るはずで、この仮定を区別する。

用途はAN4のterminal枝をevent単位で閉じる証明書の圧縮。一般rのrankや全Qを解決したとは言わない。

## 実行結果

全量化子のLean証明と別pass監査を保存。最終checkは406 jobs/2743宣言、許可3公理内。
terminal wordはAASAAA/ASAAA/SAAASAAA/SSAAAASAAAの4prefixで実際の全P2 ledgerを確認。
子unitのCPU/形式化を親journalのH-20261023-05区間に含め、別時間として加算しない。
次はr4 A-event macro simulationで、このgap上限を供給Aだけに適用する。
