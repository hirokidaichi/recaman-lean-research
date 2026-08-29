# CrossingDowncrossRefined

**役割:** ready crossingノードの保存horizon以後にdowncrossが存在する場合、その端点がfreshなbelow-target値となって履歴予算を厳密に下げ、extended-history子へのrefined stepが完成することを証明する。

## このモジュールの役割

`CrossingRefinedBoundary`は、crossingノードからの非crossing脱出には新しいbelow-target履歴値の消費(履歴予算の厳密低下)が必須であることを示した。本モジュールは、その予算低下を実際に供給する自然な機構がdowncross(下方横断: target以上の値からtarget未満の値への一歩の遷移)であることを証明する。強制加算は値を増やすだけなので下向きには動けず、downcrossの端点は必ず合法減算による未出(fresh)の値である。それがtarget未満である以上、履歴予算は厳密に減り、元のcrossingのpost-state(横断直後の状態)を代表とするextended-history normal子への正当なランク辺が得られる。

## 主要な定義

### `ReadyCrossingSearchInvariant` (L17)

crossing証明書`CrossingSearchInvariant`に、現在監査済みのすべてのrefined生成元が保持しているtarget-ready時計条件`target ≤ node.horizon + 1`(horizon-ready)を付加した状態である。用語集の「ready crossing / 時刻準備済みcrossing」に対応する。

### `FutureDowncrossStep` (L23)

保存された履歴horizon以後の真のdowncross遷移である。三条件`historyHorizon ≤ time`、`target ≤ a(time)`、`a(time+1) < target`を保持する。

## 定理と証明

### `FutureDowncrossStep.strict_budget_drop` (L31)

**主張:** 将来のdowncrossの端点は旧horizonに対してfreshであり、したがって

```text
missingBelowCount target (time+1) < missingBelowCount target historyHorizon
```

が成り立つ。すなわち、target未満の未出値の個数(履歴予算)が厳密に減る。

**証明:** まず、時刻`time → time+1`の遷移は合法減算である。もし強制加算なら`a(time+1) = a(time) + (time+1) ≥ a(time) ≥ target`となり、端点がtarget未満であることに矛盾するからである。レカマン数列の減算可能性`CanSubtract`の定義には「減算先が履歴に未出であること」が含まれるので、端点`a(time+1)`は時刻`time`までの履歴に現れていない。履歴は時間について単調(`valuesThrough`は包含で増える)なので、より早い`historyHorizon`の履歴にも現れていない。こうして端点は「target未満・`historyHorizon`では未出・`time+1`では既出」の三条件を満たし、`missingBelowCount_strict_of_new`により予算は厳密に減少する。

### `ReadyCrossingSearchInvariant.refinedStep_of_futureDowncross_withBudgetDrop` (L58)

**主張:** ready crossingノード`node`とその保存horizon以後のdowncross`hdown`(時刻`time`)が与えられたとき、targetが出現するか、またはrefined domainに属する子`child`が存在して、`node`へのランク進捗と予算の厳密低下

```text
missingBelowCount target child.horizon < missingBelowCount target node.horizon
```

を同時に満たす。予算低下を結論に明示的に残す強形であり、呼び出し側はこれを使って「anchorが下がらなかった中間crossingノード」を飛び越えられる。

**証明:** downcrossの始点で`a(time) = target`ならその時刻が出現の証人であり終了する。そうでない場合、crossing証明書から横断時刻`crossingTime`とpost-state座標を取り出し、子ノードを

```text
child = ⟨time+1, a(crossingTime+1), normal, a(crossingTime+1)⟩
```

と定める。すなわち代表時刻を`crossingTime+1`(post-crossing状態)、履歴horizonをdowncross端点の時刻`time+1`に置いたextended-history normalノードである。証明書の各条件を確認する。

- 代表 ≤ horizon: 証明書の`crossingTime + 1 < node.horizon`と`node.horizon ≤ time`から`crossingTime + 1 ≤ time + 1`。
- horizonのtarget-ready性: 親の`target ≤ node.horizon + 1`と`node.horizon ≤ time`から`target ≤ time + 2`。
- 値の下界: 厳密crossingの`target < a(crossingTime+1)`から`target ≤ a(crossingTime+1)`。
- 座標: crossing証明書のpost-state座標をそのまま使う。

ランク進捗は`strict_budget_drop`による第一成分(履歴予算)の厳密低下そのものである。予算低下も同じ事実を再掲して返す。

### `ReadyCrossingSearchInvariant.refinedStep_of_futureDowncross` (L100)

**主張:** ready crossingが保存horizon以後にdowncrossを持てば、downcrossの始点でtargetに当たるか、強制された予算低下を通じてextended-history normal子へ脱出する。すなわち`CrossingRefinedStepHypothesis`の結論の形のrefined stepが得られる。

**証明:** 前定理を適用し、結論から予算低下の成分を落とすだけである。

## 全体の中での位置づけ

証明地図の「crossing future downcross」の行に対応し、状態は「条件付き閉包済み」——downcrossの存在を仮定した枝が閉じた——である。`CrossingRefinedBoundary`が要求した予算低下を実際に構成する最初のモジュールであり、`RefinedOracleBoundary`の残余`CrossingRefinedStepHypothesis`のうち「将来downcrossがある場合」を処理する。ここで定義した`ReadyCrossingSearchInvariant`と`FutureDowncrossStep`は下流の基盤語彙になる: `CrossingBelowRefined`はhorizonがbelow-targetの場合を分類し、`CrossingTailRefined`は「downcrossが存在しない」残りの枝が恒久上方tailと同値であることを示して、強形`withBudgetDrop`を停留した中間crossingの飛び越えに用いる。`PermanentAboveTail`以降のzero-budget解析も本モジュールの構造の上に立つ。
