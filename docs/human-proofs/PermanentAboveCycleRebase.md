# PermanentAboveCycleRebase

**役割:** canonical return crossingを次の親に据え直すrebase操作が意味論的に正当である(旧zero-budget horizon・permanent tail・最小値証明書を保存する)ことを検証し、同時に、rebase後の再生は必ず文字どおりのstationary kernelに帰着してcycle退出にならないという、この修復の正確な限界を証明する。

## このモジュールの役割

`PermanentAboveCycleExit.lean`は、discharge退出の失敗を三つの型付きkernel残余(anchor厳密成長・時系列不適格・文字どおりの停留)に分類した。このうち前二者への最も直接的な修復候補は、canonical return crossing自身を次の親crossingにするrebase(据え直し)である。本モジュールはこの修復を二面から確定する。正の面では、rebaseは意味論的に正当である: return crossingは親と同じzero-budget horizonの上でready crossingとして成立し、permanent tail証明書・最小値証明書・combined証明書がすべてそのまま移送される。負の面では、rebaseされたcanonical親から同じhistorical dischargeを再生すると、canonical選択の一意性により同一のcrossingが返る。すなわちrebaseはすべてのdischarge証明書を無条件に文字どおりのstationary kernelへ正規化するが、そのkernel自体を消去することはできない。これにより、残る未証明点は「canonical crossingにおけるstationary kernelの解消」ただ一点に絞られる。

## 主要な定義

### `CanonicalReturnRebaseCertificate` (L22)

discharge証明書`source`をそのcanonical return crossingへrebaseした結果の完全な型付きデータ。rebase後のnode

```text
rebased = ⟨parent.horizon, a(source.returnTime), normal, a(source.returnTime)⟩
```

(horizonは旧親のまま、anchorはreturn crossingのpredecessor値)と、`rebased`上へ移送されたcombined証明書、`rebased`を親とする新しいdischarge証明書を保持する。さらに、新旧の証明書が同じ歴史データを共有すること(`same_tail_start`、`same_down_time`、`same_return_time`)、新しい親のold crossingがreturn自身であること(`old_is_return`)、anchor一致(`a(returnTime) = rebased.anchorParent`)、crossing時刻一致(`returnTime = oldCrossingTime`)、そして新しいdischarge証明書がstationary kernel残余(`CanonicalDischargeKernelResidual`)に属することを等式群として明示する。

## 定理と証明

### `PermanentTailDischargeReturnCertificate.exists_canonicalReturnRebase` (L41)

**主張:** すべてのdischarge証明書について、canonical returnを旧horizon上のready zero-budget crossingとして据え付けるrebase証明書が存在する: `Nonempty (CanonicalReturnRebaseCertificate h)`。旧permanent-tailデータと最小値データはすべて保存される。

**証明:** 三段階で構成する。

*rebased nodeがready crossingであること。* return crossingの着地値`a(returnTime + 1)`はtarget以上であり、targetは未出なので実は厳密に上。また`target ∉ valuesThrough returnTime`。着地時刻の商剰余座標を取り、`return_before_parentHorizon`(`PermanentAboveCycleExit.lean`)から`returnTime + 1 < parent.horizon`なので、`CrossingRecoveryInvariant`の全条件(target未出、強制加算、厳密crossing、座標、horizon前、predecessor < anchor)が揃う。clock条件`target ≤ horizon + 1`は旧combined crossingのready性からhorizonが同一のまま継承される。

*permanent-tail証明書の移送。* `PermanentTailCrossingCertificate`の残りの条件(horizonがtail内、予算0、horizonの値が厳密上方、future downcross不在)はすべてhorizonだけの関数であり、rebased nodeのhorizonは旧親と同一なので、旧証明書のフィールドがそのまま通用する。tail本体と最小値証明書も変わらないので、combined証明書が`rebased`上で成立する。

*新しいdischarge証明書とその停留性。* 新証明書は旧証明書の歴史データ(tailStart、downcross、endpoint、return crossing)を全部再利用し、`oldCrossingTime`だけを`returnTime`に置き換える。return crossingは時刻0からのweak upcrossingとも見なせるので`old_crossing`フィールドを満たし、anchor等式は`rebased`の定義から自明。最後に、新しい親のold crossingはこのendpoint からのcanonical crossingそのもの(`return_crossing`自身)なので、`kernelStationary_of_oldCanonical`(`PermanentAboveCycleExit.lean`)が新証明書のstationary kernel残余を与える。全等式フィールドは構成上`rfl`である。

### `PermanentTailDischargeReturnCertificate.exists_rebasedStationaryKernel` (L151)

**主張:** anchor成長残余や時系列不適格残余を含むすべてのdischarge証明書は、文字どおりのstationary kernelへの無条件の正規化を持つ。すなわちrebase証明書であって、`rebased`上のcombined証明書、anchor一致`a(returnTime) = rebased.anchorParent`、crossing時刻一致`returnTime = oldCrossingTime`、およびstationary kernel残余を同時に満たすものが存在する。

**証明:** L41のrebase証明書の該当フィールドを並べるだけである。要点は前提の無条件性にある: 元のkernelがどの枝(成長・時系列・停留)にあったかを問わず、一回のrebaseで必ず「canonicalな親のもとでの文字どおりの停留」という単一の標準形に到達する。三種の障害が一種に正規化されたことになる。

### `PermanentTailDischargeReturnCertificate.exists_rebase_with_noCycleExit` (L166)

**主張:** より直接に、型付きrebaseは常に存在し、その再生はcursor精密化されたcycle(`TailCursorCycleProgress`)の正当な退出ではない。すなわちrebase後のdischarge nodeからreturn crossing nodeへの進捗は成り立たない。

**証明:** L41のrebase証明書を取り、crossing時刻一致`returnTime = oldCrossingTime`で書き換えると、子と親のcursorは同一のanchor・同一のcrossing時刻を持つ。`tailCursorCycle_no_stationary_exit`(`PermanentAboveCycleExit.lean`)がこの形の退出を禁止する。

したがってrebaseは「修復」ではなく「正規化」である: kernelの三枝を一枝に集約するが、その一枝(canonical crossingでの停留)を突破するには、rebaseの反復でもcursor rankでもない、真に新しい下降量または軌道論的議論が必要である。

## 全体の中での位置づけ

本モジュールはpermanent above-target tail解析ファミリーの現時点での終端であり、`PermanentAboveCycleExit.lean`の三枝kernelを入力として、その標準形を確定する。系譜をまとめると: `PermanentAboveTail`が仮想反例のtail内部からzero-budget crossingとhistorical blockerを抽出し、`PermanentAboveHistory`がblockerの反復を有限化して停留残余を発見し、`PermanentAboveCanonical`がearliest選択とdual budgetを与え、`PermanentAboveCycleRank`と`PermanentAboveCycleExit`が整礎rankを精密化して退出失敗を型付きkernelへ分類した。本モジュールの結論により、全射性予想への現在の残余は「canonicalな親のもとでのstationary kernel — すなわち、canonical return crossingを親としたときに同一のcanonical crossingしか再生されない状況 — から、strictなcursor下降または新しい整礎量をどう構成するか」という単一の問いに縮約された。これが次の証明エポックの出発点である。
