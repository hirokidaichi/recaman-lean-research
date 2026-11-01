# Hypothesis card: 残りA予算を保持するlocal context消去

- ID: H-20261025-03
- Status: PROVED-LEAN（全future local消去のE-402）/ COMPUTED（商graph E-403）
- Parent: R-20261025-01、H02、E-390、一般C1/r4分類の圧縮入力
- Mode: 局所探索。最大25分で安全な商と実測削減を判定し、失敗なら別のrun-familyへ切替。

## 一問・量化子

任意有限語u/v、B≥0について、vのmass + uの全suffixの最大mass + B≤0なら、
任意未来語x（ones(x)≤B）に対してlocalSupply(u++v++x)=localSupply(v++x)か。
suffix最大massは空suffixも含めた具体な再帰関数で供給し、未証明のdefined Propにしない。
これを満たす最短suffixを返す有限contextTrim(B,w)を実装し、全未来xへの同値を証明する。

モデル評価ではA≤10までの残り予算B=10−Aを使い、A11遷移は切らずwitnessで停止。
local用contextと、old signature用の実総mass/area/A/Sを分ける。
S19飽和後はoldなし、old用areaを捨てる。trim contextのmassを実総massと混同しない。
各遷移で未来同値を維持し、短いcontextだけの現在タグ一致で全future保存と推定しない。

## 紙上chain・受入

u内から始まる全suffixのmass≤ceiling(u)。v++xがこれを相殺しP2のmass1を排除する。
条件付きの消去を有限個のsplitで選ぶこと自体も全未来の同値を保持する。
一様19trimは既証明E390とtrim_appendで全未来A≤10に対して安全。
モデルへの実装は独立reverse式との全遷移照合、旧状態/辺の前向きsimulation、飽和/実E395/A11対照で攻撃する。
小さい商が実測できなければ同じkernel法を再開しない。計算結果はCOMPUTED、kernel結果を先取りしない。

## 反証・費用

u/v空、B0、等号、混合prefix、A予算を1超える未来、S19/20と未使用長gapを実行前protocolで固定。
新規CPU探索は当初0。必要時はsource/argv/dirty hash・独立holdout・CPU/wall/state/RSS上限を別protocolへ先に保存。
25分以内に数学的保存または具体削減がなければSTOPPED。修理は一回まで。
別pass監査10分を残し、親cycleへ費用を二重計上しない。一般C1/az>=5は未解決。

## 06:25時点の測定

suffix最大massと残りA予算に対する全future消去・contextTrim保存は個別Lean成功。空語/B0/境界と、予算を無視するS|S|AAAASの反例を紙上反証passで保持。独立有限future discovery420/holdout1920、未使用長gap520、旧12837状態との全product辺照合が成功。新商10106状態/35440辺、全16endpointでcontextが全文であることも照合。A11を切らない。生成0.36CPU秒・独立2.45CPU秒、cap70内。全r4分類はまだkernel未供給。単に新表を時間追加で検査せず、H04でlookupを除くproof DAGをbenchする。

## 最終意味監査

残りA予算付きの全future local同値はE-402で証明、商はE-403の有限照合。old用実総mass/areaは別保持。
商自体の全kernel simulation/初期証明は供給しておらず、別の元graphのE-404判定を商の証明と呼ばない。
予算なしの弱化はE-405の一様反例族でREFUTED。次は10/26カードの元基点free-gapへ。

## 当日journal確定実績
親cycle R-20261025-01: 06:01:21.862027〜07:59:10.380882、確認済み117分48.519秒、不足2分11.481秒。
このcardを別cycleとして加算せず、実unit/phaseの内訳は[当日DAILY](RESEARCH_HANDOFF_2026-10-25_DAILY.md)と[journal](data/daily_research/2026-10-25.json)を参照。待機・未確認・CPU・前日分の加算なし。
