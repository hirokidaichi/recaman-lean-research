# PermanentAboveCorridorReplayFloor

**役割:** replay crossingが実軌道のイベントであることを利用し、kernel計算による排除を「実際のstepの向き」「またがれるtargetの実出現」まで拡張して、crossing clock ≥ 6・target ≥ 8の下限を確立する。上側は三角包絡`target ≤ upperTri(clock + 1)`で押さえ、固定点の二パラメータを両側から挟む。

## このモジュールの役割

`PermanentAboveCorridorReplayCorridor.lean`はclock境界`clock + 1 < a(clock)`の数値検証だけでclock ≥ 3・target ≥ 5を得た。しかしreplay証明書はそれ以上の実軌道的事実を保持している: crossing stepは本物の強制加算であり(`forced_addition_at_crossing`)、crossingは実際にtargetをまたぎ(`crossing_straddles_target`)、そしてそのtargetは全軌道で未出である(tail証明書の`target_missing`)。これらはいずれも具体的なclockの上では決定可能な命題なので、Leanカーネルの`decide`で床をさらに引き上げられる。clock 4は値境界に反し(`a(4) = 2`)、clock 3は値境界こそ通るが実際の軌道stepが減算である(`a(4) = 2 ≠ a(3) + 4`)。clock 5はまたぎ得るtargetが`8..13`の6個に限られるが、その全員が時刻16までに実軌道に出現するため、missing-target仮定と矛盾する。従ってclock ≥ 6、target ≥ 8である。他方、軌道値には三角数の包絡上界`a(n) ≤ upperTri(n)`があるので、またがれたtargetは`upperTri(clock + 1)`以下でもある。replay固定点のclockとtargetは下からも上からも挟撃された有限領域に閉じ込められる。

本モジュールの定理はすべて`TerminalExactDischargeReplayCertificate`のnamespace内にあり、replay証明書`r`のメソッドとして書かれている。

## 定理と証明

### `target_missing` (L31)

**主張:** replayは仮想反例の内部に住んでいる: そのtargetは全軌道で未出である。

**証明:** discharge証明書のcombined tail(`MissingPermanentAboveTail`)の`target_missing`フィールドの射影。以後のkernel排除で「またいだtargetが実は出現している」ことを矛盾として使うための前提である。

### `target_le_upperTri` (L38)

**主張:** 三角包絡による上界: `target ≤ upperTri(crossingTime + 1)`。

**証明:** straddleの上側`target ≤ a(crossingTime + 1)`と、軌道の一般上界`a(n) ≤ upperTri(n)`(`upperTri(n) = n(n+1)/2`に対応する再帰的三角数)の推移律。下限定理と合わせると、各targetについてreplay可能なclockは有限区間に限られる。

### `five_le_crossingTime` (L44)

**主張:** clock 3と4は実軌道stepにより排除される: `5 ≤ crossingTime`。

**証明:** 前モジュールの`three_le_crossingTime`でclockは3以上。残る`crossingTime ∈ {3, 4}`をそれぞれ潰す。

- `crossingTime = 3`: replayは強制加算の等式`a(4) = a(3) + 4`を要求するが、実軌道は`a(3) = 6`、`a(4) = 2`(時刻4は合法減算)なので`decide`で偽。
- `crossingTime = 4`: 値境界`5 < a(4)`を要求するが`a(4) = 2`なので`decide`で偽。

すなわちclock 4は「値が小さすぎる」、clock 3は「値は足りるが実際のstepの向きが逆」という、それぞれ別の実軌道的理由で消える。

### `six_le_crossingTime` (L61)

**主張:** clock 5もまたがれるtargetの実出現により排除される: `6 ≤ crossingTime`。

**証明:** `crossingTime = 5`と仮定する。straddleは`a(5) < target ≤ a(6)`となり、実値`a(5) = 7`、`a(6) = 13`から`target ∈ {8, 9, 10, 11, 12, 13}`。しかしこの6個はすべて軌道の初期部分に実出現する:

```text
a(16) = 8,  a(14) = 9,  a(12) = 10,  a(10) = 11,  a(8) = 12,  a(6) = 13
```

いずれもLeanカーネルの`decide`で検証され、それぞれがL31の`target_missing`と矛盾する。よってclock 5のreplayは存在しない。

### `eight_le_target` (L90)

**主張:** replay固定点がまたぐtargetは8以上である。

**証明:** L61の`6 ≤ crossingTime`と前モジュールの`crossingTime + 1 < target`から`8 ≤ target`。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「replay kernel floor(clock/targetを両側から挟撃済み)」に対応する。上流は`PermanentAboveCorridorReplayCorridor.lean`(初期帯への閉じ込めとclock ≥ 3)である。証明手法の観点では、`PermanentAboveCorridorFiniteClosure.lean`が「finite窓 → target ∈ {4,5} → `a(131) = 4`, `a(129) = 5`で矛盾」とやったのと同じ「抽象的残余を具体的軌道値の検証区間へ絞ってからkernelで殺す」戦略の、replay固定点への適用第二歩である。下流の`PermanentAboveCorridorReplayInterface.lean`はこの床の上でmissing-target interfaceを確定し、replay枝の一意性を示す。clockの下限をさらに押し上げる(あるいは`target ≤ upperTri(clock+1)`との併用で特定のtarget帯を全滅させる)ことは、同じ形の`decide`検証を追加するだけで機械的に続けられる構造になっており、replay固定点を有限検証で完全排除できるかがこの系列の焦点である。
