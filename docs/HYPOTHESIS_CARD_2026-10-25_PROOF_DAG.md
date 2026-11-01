# Hypothesis card: 表lookupを除いたA-event証明DAG

- ID: H-20261025-04
- Status: STOPPED（当日方法）。分類の命題E-404はCONJECTURED
- Parent: R-20261025-01、r4分類/E-388/E-390/E-392、H03の商評価
- Mode: C1活用。最初15分で256閉nodeの実資源を測り、改善なしなら停止してrun-familyへ切替。

## 一問・量化子と受入

任意padded BlockWord実prefix後の正不足excursion、元0基点の非Endable A≤4、終端不足1なら
語長によらずsegが明示16終端語のいずれかとなる、というE-388の分類をkernelで検査できるか。
過去の12837状態/40macro辺の数値入力は再利用するがCOMPUTEDのままであり、各辺と初期証明を新checkerで供給する。
H03商は21%減に留まり実語simulationも別に要るため、まず既証明E-390が直接消費できる旧状態を新DAG方式で検査する。

全Aは各macroで1増える。各具体stateにgood（A≤10、S≤19、free≤4、gap0正規、全gapの終端16語判定）と
全successorの既証明Checkedを持たせた正の帰納的証明を構成する。
global Table.get、巨大Nat payload、全表展開を使わず、各stateの具体定義と子証明定数を共有する。
初期Checkedを実際に供給する前に、Checked仮定付きreductionだけを進展/分類と扱わない。
実語adapterはE-390の全A≤10を前prefixの帰納不変量から供給し、全入力のA≤10を仮定しない。
最終受入は初期kernel証明、実語全長分類、必要Audit/G5、./scripts/check.sh成功。
16語からのQはE-392を消費し、一般az≥5/C1全体を解決扱いにしない。

## 反証・停止・費用

全macroのA0/A1とgap0..19を検査。長gap後free AとA11を元定義のまま保持。
goodがA11を拒否すること、子リストを欠落させた証明がkernelで拒否されることを小負例で確認。
旧graphは独立reverse/実E395対照を保持、同じデータを新しいholdoutとは呼ばない。
checker source/argv/dirty hashと資源測定を実行前に凍結。bench CPU/wall90秒、全体はbench改善を確認した場合のみ別capを固定。
RSS4GiBまたは期限guardで自分のprocessだけを止める。上限増加だけの再開をしない。修理は数学1回まで。
親の残り活用から実測/検証を支払い、監査・引継ぎを残す。07:45以降に新数学を始めず08:00厳守。

## 最終判定（07:45 JST）

同じ全12837nodeの初期証明は未供給。layer版はA4〜10の11316nodeをkernel検査したが、A3以下/初期Checked/実語footerは完了前に固定07:45期限で停止。864.548wall秒、peak3701456KiB。RSS上限追加はしていない。この方法を当日STOPPEDとし、分類はCONJECTURED/E388 COMPUTEDを保持。
全sourceをpacket layered_sourceへbyte/hash付き隔離。条件付きreductionや部分層を無条件の分類と数えない。再開は独立数学的pruning/小商等で測定改善がある時に限り、同じ未完了jobへの時間追加はしない。次は10/26 free-gapカード。

## 当日journal確定実績
親cycle R-20261025-01: 06:01:21.862027〜07:59:10.380882、確認済み117分48.519秒、不足2分11.481秒。
このcardを別cycleとして加算せず、実unit/phaseの内訳は[当日DAILY](RESEARCH_HANDOFF_2026-10-25_DAILY.md)と[journal](data/daily_research/2026-10-25.json)を参照。待機・未確認・CPU・前日分の加算なし。
