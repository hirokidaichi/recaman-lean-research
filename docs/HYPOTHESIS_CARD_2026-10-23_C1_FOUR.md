# Hypothesis card: r≤4のQを独立old signatureで計算監査

- ID: H-20261023-04 / cycle R-20261023-01（局所探索枠内、親と二重計上しない）
- Status: COMPUTED（E-388）。kernel未検査のr4分類はPROVED-LEANへ昇格しない。
- Frozen: 2026-10-23 07:16 JST、計算前。

## 一問・受入・停止

H-20261023-02と同じ元0基点の全P2、prefix文法、正不足、qで不足1、Ay≤1、Fb≤Fnで、
Azの非Endable A上限を4へしたQが、深さ4内の全futureで独立old signature緩和にも成立するか。
初期語はH-20261023-03の完了・独立照合済み緩和から得た16語に固定する。
受入は全遷移を含む完了木と別実装の一致、または具体的な緩和Z<0 witness。
語長/S数のcutoffなし。CPU各30秒/経過28秒、stack512/50万状態は保護guardで、到達は未完了。
source/argv/hashをQ4_RUNS.jsonへ実行前固定。同じ当日CPU240秒上限内。

全lengthのr4深さ供給も現時点ではCOMPUTED依存。将来が深さ4を外れる場合は既存E-379へ
接続する紙上chainを確認するが、全Q4をLean証明済みとは呼ばない。
反例が緩和の自由old選択だけで生じたら、親Qの反例と区別し共通prefixが次の未知edgeとなる。

次はSのみのgap後に供給が可能なclockを有限化する別unitへ移り、同じAN上限の延長を繰り返さない。

## 実行結果

719状態・572guard・Z最小1、最大語長22で全木完了。別forward実装で全状態/全edge一致。
CPU/argv/hash/rawはQ4_RUNS.json等に保存。親H-20261023-03内の子計算として実行し、独立の作業分を二重加算しない。
全Q4への深さ外の接続はE-379の紙上chain。r4深さ分類のkernel証明書化は次回のまま。
