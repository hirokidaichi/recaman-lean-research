# Hypothesis card: 加算回数の依存layerごとの証明保存

- ID: H-20261025-10
- Status: STOPPED（当日方法）。分類の命題E-404はCONJECTURED
- Parent: R-20261025-01、E404の同じr4分類、H09の全macro同値。
- Mode: 検証工学。single-file方式は4GiBでSTOPPED。上限を増やさず、保持するelaboration環境を分ける。

## 一問・数学の保存

全macroの子は全Aが厳密に1増える。A=10から0の11依存layerに分け、
各layerのkernel検査済みopaque子証明を次layerでimportすれば、同じ12837node/同じchild/同じ実語adapterを
4GiB以内で保存できるか。各layer最大6959node（A4）、A5は3358。
Checked定義/good/全40候補の意味/16語/実語の全量化子/初期証明は変更しない。
データ定義と子証明を公開名へ置き換えるだけで数学的仮定を追加しない。定理数/ファイル数を成果に数えない。
single-file源/失敗logを隔離し、layer列と最終初期証明が全てkernel成功する前にはE404を昇格しない。

## 受入・停止・費用

A10/9/8の64node（閉じた依存列）を先に検査し、importを介した同じ具体証明と低いRSSを実測する。
成功した場合だけ残りを全体検査する。bench90CPU/90wall、全体900CPU/900wall、RSS4GiBを実行前固定。
親の合計上限990秒は旧1200秒を増やさない。各回7:45で自分のprocessを止め、8時延長なし。
失敗ならこの環境分割法もSTOPPEDとして、未検証sourceをpacketへ隔離し、一般不等式の検証/引継ぎへ移る。
stage/commit/pushはしない。commitの1module/30分制限を変更・迂回しない。

## 最終判定（07:45 JST）

同じ全12837nodeの初期証明は未供給。layer版はA4〜10の11316nodeをkernel検査したが、A3以下/初期Checked/実語footerは完了前に固定07:45期限で停止。864.548wall秒、peak3701456KiB。RSS上限追加はしていない。この方法を当日STOPPEDとし、分類はCONJECTURED/E388 COMPUTEDを保持。
全sourceをpacket layered_sourceへbyte/hash付き隔離。条件付きreductionや部分層を無条件の分類と数えない。再開は独立数学的pruning/小商等で測定改善がある時に限り、同じ未完了jobへの時間追加はしない。次は10/26 free-gapカード。

## 当日journal確定実績
親cycle R-20261025-01: 06:01:21.862027〜07:59:10.380882、確認済み117分48.519秒、不足2分11.481秒。
このcardを別cycleとして加算せず、実unit/phaseの内訳は[当日DAILY](RESEARCH_HANDOFF_2026-10-25_DAILY.md)と[journal](data/daily_research/2026-10-25.json)を参照。待機・未確認・CPU・前日分の加算なし。
