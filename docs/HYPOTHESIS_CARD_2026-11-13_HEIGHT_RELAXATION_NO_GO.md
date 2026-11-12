# H-20261113-04: 高さ別必要会計だけの無重み化を反証する

- Status REFUTED (height-relaxation inference only; actual claim remains separate)
- Parent H-20261113-02; first general block / distinct analytic falsifier
- Bounded question: E674の全高さ必要式・A=E+F・歩みの上下段保存・全prefix正不足だけから、深さに依存しないA<=cFを導けるか。

## Exact proposed mechanism and acceptance
任意の有限±1語と高さ別非負整数A_h,E_h,F_h。A_hは語の実A数、0<=E_h<=A_h、F_h=A_h-E_h。E_hはここでは供給の**宣言mark**でありEndNと同一視しない。全hで
E_h<=Σ_{l<=h-2}(2(h-l)-3)A_l
と、全非空prefixでS数>=宣言E数+1を要求する。実語を用いるので段を飛ばさず、上下crossingの保存も保持する。
この入力群だけから全深さ共通の有限cでΣA_h<=cΣF_hが従う、という推論機構を判定する。
受入は全cを破る明示族と、全入力の完全検証。新しい元EndN反例・C1反例とは呼ばない。

## Frozen candidate family / falsifier
m>=3、元語S^m A^m、境界n=0（空BlockWord）、高さ原点を谷底へ移す。各A高さ0..m-1を一度ずつ通る。高さ0,1はfree mark、高さ2..m-1はsupplied markと仮置きする。小境界m=3/6/7を検査し、全mへ紙上で量化する。元Winのsource時計・面積を最後に戻し、この族で欠落する仮定を特定する。

## Stop / cost / consumer
worker追加なし、探索予算8CPU秒の残余を自動使用しない。紙上証明20分上限。必要式を満たさない、既知と同じ反例、又は単なる有限不在なら一般化進展にしない。
証拠が出れば高さ別不等式だけを合算する案を停止し、次consumerは元source/clockを保持する多窓会計・深さ操作へ。係数3の元actual仮説H-03は別にCONJECTUREDを保つ。純算術helper単独のG3 rowやdummy wrapperを作らない。

## First result / proposer-falsifier verdict
- 否定対象の推論機構はREFUTED。全m>=3のS^m A^m、宣言F=2/A=m/E=m-2が全高さ必要式・実walk-flow・prefix正不足を満たす。任意cにm>2cで破る。完全紙上証明は当日DEPTH_ACCOUNTING note。
- 元EndNでは供給1/free=m-1であり、元倍率3は反証しない。元source-clock/areaを忘れた緩和モデルに限定する。人間レビュー未。
- 一般化判定候補: 全深さ一様会計をこの必要入力だけで導く機構のno-go。最終独立auditで判定確定。registryはaudit後。Lean純算術moduleは作らない。
