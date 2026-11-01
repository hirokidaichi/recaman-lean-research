# 2026-10-25: C1の供給間隔と有限分類の検証

## 新しい一般入力

E-407（PROVED-LEAN）は、padded BlockWord実prefixから続く語で、先行する全AをAとすると、
Sがj個続いた後に実供給Aがあるためには 2j+2≤A が必要であると証明した。
語長・深さ・free予算・A・jの上限はない。旧E-389のj≤2A−2をj≤floor(A/2)−1へ強化した。
S^(j+1) A^(2j+2) S^j のlocal供給が全jで等号となるため、この全Aだけによる上界は鋭い。

local側はkey=2area+mass(mass−1)がSで変化しないこと、zero-key/正massなら2mass≤Aであることを用いた。
old側も必要signatureの二次不等式から同じ上界を供給し、最後に実EndNへ接続した。
全Aと非供給Aは異なる。一般rの供給連鎖rankやC1が証明されたわけではない。

## 他の安定した入力

- E-401/E-406（PROVED-LEAN）: 任意の前置語に十分なS separatorと偶数A-runを続けた形で、追加free0なら任意長の未来の全A≤1。
  E-406は実総Sとsuffix最大massを分離し、無制限二run族で短いseparator条件を供給した。任意tailへの形の供給は残る。
- E-402（PROVED-LEAN）: 明示残りA予算付きなら、深く負になったlocal文脈を全未来で双方向に消去できる。old用の総mass/areaは別保持が必要。
- E-405（REFUTED）: 予算を外す案は任意に深い負bufferでも反例族がある。一般C1や実軌道の反例ではない。
- E-400/E-403（COMPUTED）: 固定10代表は1状態しか削れず同大表法を停止。一方、未来local文脈商は12837→10106状態、全辺の独立照合と別gap対照成功。
  商の全kernel証明は未供給。既存graphを独立な新しいholdoutとは呼ばない。

## r4検証の扱い

最終結果は[当日DAILY](RESEARCH_HANDOFF_2026-10-25_DAILY.md)とE-404を正本とする。
数値graphの存在だけでは全長分類を証明できない。実全wordからmacroへのsimulation、全具体子のkernel証明、
初期Checkedの供給、実語adapter、Audit/G5/全体checkを区別する。
16候補への全包含であり、16候補全ての実現を主張しない。
単一fileの資源停止は数学的な反例ではない。測定済みのscan/pruning/依存layer分割は同じ元40macroと全childを保つ。

## C1との接続と次の未知edge

C1はSLのd1の一部であり、HにはC2/TSを含む別の未解決入力も残る。
有限free予算の一段拡張と一般の供給間隔上界は、無制限rankの材料を増やすが、任意rの帰納を供給しない。
次は[H-20261026-01](HYPOTHESIS_CARD_2026-10-26_FREE_GAP.md)の j+1≤先行free A数。
真の元基点履歴とpositive deficitを維持し、まず反証する。全A≤2rや結論を入力にして埋めない。
