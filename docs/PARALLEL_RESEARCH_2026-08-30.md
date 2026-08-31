# 並列研究監査 2026-08-30

## 結論

ledger、blocker、有限反例モデル、負potential障壁を独立に監査し、派生した二つの集中命題も追加調査した。全域性へ直結する決定打は得られていないが、次の境界は明確になった。

1. least-missing反例のtail minimumは、任意の高商状態ではなく `q ≤ 1`, `G ≥ -1` に入る。このcheckpointとledger corridorはLean化した。
2. 自由な初期履歴を許す局所モデルには、履歴サイズ・parity・上界・ledger単調性を満たす任意長擬似反例がある。
3. 従って、局所遷移と静的履歴条件だけからの証明は停止できる。必要なのは実prefixの因果的到達可能性である。
4. blockerの固定容量とreset一対一対応は反例で棄却された。subtraction massによるinterval matchingは2,000万項まで必要最小定数`C_H^*=9`、唯一の最悪例`[2,6]`を保った。
5. 全軌道の `q ≥ 6 → G ≥ 0` は強い経験的候補だが、H6の21合同類すべてに局所条件を満たす抽象モデルがある。独立枝は停止し、blocker provenance問題へ統合する。
6. canonical least-tailでは`a_t < t+target`が既に従うため、`q=1,r>target`のhigh-blocker枝は空である。一般tail用provenance定理をcanonical主線の進展とは数えない。
7. 初期releaseを切ったall-job Hall scanは500万項までsharpな`C=3`へ下がった。真なら`liminf a_n/n≤3`を与えるがpermanent-above tailとは矛盾せず、直接証明枝は停止条件に到達した。

## A. least-tail minimum と ledger

`s` を最小の permanent-above tail start、`t` をそのtailのminimum時刻とする。既存の最小tail startとその直前値を結合すると、

\[
target+2\le a_t\le a_s\le target+s-1<2s\le2t.
\]

従って `CoordinatesAt t q r` に対して

\[
q\le1,\qquad G(q,r)\ge-1.
\]

負potentialが残るのは `q=1, r=0, a_t=t, G=-1` の一点形だけである。ledgerでは

\[
2\,subSum(t)+target+2\le U(t)<2\,subSum(t)+2t.
\]

よって反例tailのminimum checkpointでは、weighted subtraction massは全clock質量の半分から線形誤差以内にある。

一方、tail-minimum区間で「少なくとも半分がsubtraction」は偽だった。最初の反例は `[5,131]` で、126 step中61 subtractionである。高さ差が区間長に比例するという候補も `[132,99734]` で破れる。ledgerとminimumだけでは直接矛盾まで届かない。

評価: checkpointの構造価値 **85/100**、全域性への直接寄与 **15/100**。

このcheckpointは`LeastTailLedgerMinimum`として形式化した。さらに`q≤1`を分解すると、

- `q=0`、または`q=1,r≤target`なら`a_t≤t+target`
- `q=1,r>target`なら最初のforced stepの候補`r-1`はpositiveかつ既出であり、
  `target≤r-1<a_t`を満たすfirst occurrenceが時刻`t`より前にある

が得られる。この二分もLean化済みである。一般strict tailでは後者をexact ledger payment、3-clock gap、
historical downcrossまたはrenewed tail、既存tail-cycle rankへ接続できることもLean化した。

ただし`LeastMissingTarget`から取るcanonical witnessは

\[
a_t+1\le target+s,\qquad s\le t
\]

なので常に`a_t<t+target`である。従って座標は

\[
q=0\quad\text{または}\quad(q=1\land r<target)
\]

に限られ、high-blocker右枝は空である。この追加監査は
`exists_leastTailLedgerMinimum_lowCoordinates`として形式化した。一般provenance定理は
below-target coverageを引き継がないnoncanonical tail用の部分定理であり、canonical主線の進展とは数えない。

## B. blocker 償却

positive forced-addition clock `n` の blockerを

\[
b_n=a_{n-1}-n>0
\]

とし、最後の出現を `ℓ_n` とする。

### 棄却

- blocker固有の固定容量: blocker `1` は非常に遅いclockでも再利用され、固定予算は発散する。
- reset一対一対応: last occurrenceと再利用の間にnonpositive resetがないedgeが500万項までに30,105本あった。
- 区間の非交差部分族: subtraction clockの被覆重複はhorizonとともに増大する。

### 生存した候補

各edgeには厳密に

\[
2(subSum(n-1)-subSum(\ell_n))=U(n-1)-U(\ell_n)-n
\]

があり、`ℓ_n ≤ n-4` からedge単体の需要は区間内subtraction massで支払える。

jobを

\[
(release,deadline,demand)=(\ell_n+1,n-1,n)
\]

とし、subtraction clock `k` の容量を `k+C` とするinterval Hall条件は

\[
\sum_{r_n\ge p,\ d_n\le q}n
\le
\sum_{p\le k\le q,\ k\;sub}(k+C).
\]

`C=8` は区間 `[2,6]` で失敗する。exact range-max scanではall jobsとfirst jobsの双方で、
1千、1万、10万、100万、200万、500万、1千万、2千万の全horizonに対し必要最小定数は
`C_H^*=9`だった。最悪区間は常に`[2,6]`で、需要13、subtraction mass 4、subtraction count 1、
従って`C=8`でresidual 1、`C=9`でslack 0である。同じlast occurrenceを共有する後続jobは
互いに素なannulusへ分解できるため、残る問題は異なるblocker episodeの最初のwindow congestionである。

評価: generic blocker multigraph **42/100**、interval matching **62/100**。定数の存在を示す経験的根拠は
強くなったが、first-familyは除いたannulus jobの容量を予約しない緩和問題である。次の一回は、有限初期部を
切り離したfirst-window congestionのcausal inequalityに限る。

追加のexact scanでは、区間左端を7以後へ切った**all-job family**で500万項まで

\[
\sum_{r_n\ge p,\ d_n\le q}n
\le
\sum_{p\le k\le q,\ k\;sub}(k+3),\qquad p\ge7
\]

が成立し、必要最小定数は常にsharpな`C=3`だった。最悪例は`[16,18]`, `[111,113]`,
`[1227,1229]`などの単一job `−,+,+` 三歩形である。lazy scanは`H=100`, `C=0,…,12`の
全区間brute forceと照合した。自由初期履歴では`a_6=100`とsynthetic last-occurrenceをseedすると
`[7,15]`で需要41、容量37となり破れるため、これは静的seen-setやledgerの帰結ではない。

この`TailHall₃`を仮定すると、old blockerとnonpositive additionを例外として正確に残したまま

\[
a_{q+1}\le a_{p-1}+P_{old}+N+3Q
\]

が得られる。例外が無限なら`a_n≤2n+O(1)`のcheckpointが無限にあり、有限なら最終的に
`a_n≤3n+O(1)`となる。従って`liminf a_n/n≤3`は従うが、固定値を避けるpermanent-above tailとは
両立する。評価は独立部分定理 **70/100**、全域性への直接経路 **25/100**。大規模なprefix再構築を
投じず、短い局所chargeが見つかる場合だけ部分定理として再開する。

## C. 任意長擬似反例

任意の `L ≥ 1` に対し

\[
n=4(L+4),\qquad x_0=6n,
\]

\[
b_i=(i+4)n+\frac{i(i-3)}2\quad(1\le i\le L)
\]

とし、抽象状態の初期履歴を

\[
H=\{0,1,6n,b_1,\ldots,b_L\}
\]

とする。`Basic.step`と同じ正確な局所判定で、以後 `L` 回はすべてforced additionになる。target `2` は出現せず、全tail値は2より上にある。

さらに

\[
|H|=L+3\le n+1,
\]

全blockerは `U(n)` 以下で、parityと個別の仮想出現時刻、選択ledger値の単調性も `L=5000` まで同時に満たせた。

この族が破るのは、履歴集合が初期状態0から正確なRecamán規則で共同生成されたという因果的到達可能性だけである。

評価: 正確な有限solverによる直接証明 **20/100**、戦略フィルタ **90/100**。局所interfaceからの一様returnを狙う枝は停止する。

## H. 高商負potential障壁

exact scanでは10億項まで

- `min G=-15` at `n=99741`
- negative stateはすべて `q≤5`
- 最初の `q=8` は `n=409493529`

だった。従って

\[
q\ge6\Longrightarrow G\ge0
\]

は強い経験的候補である。成立すれば全体で `G≥-15`、従って

\[
U(q)\le r+15<n+15
\]

から `q=O(\sqrt n)` と `a_n=O(n^{3/2})` が得られる。

最小反例 `CoordinatesAt N Q s`, `Q≥6`, `G<0` を仮定すると、直前遷移は必ずregular forced additionで、

\[
a_{N-1}=N(Q-1)+s,
\qquad blocker=N(Q-2)+s.
\]

`Q=6` は `0≤s<21` の21本のaffine chordへ有限化できる。一方 `Q≥7` では幅 `2Q-1` のstripがすべてのQに残り、Q=6へ再帰縮約されない。hard residualはblockerが実prefixで以前に生成されたことを排除するhistory lemmaで、枝A/Bへ合流する。

H6の追加監査では、parityとledgerから

\[
N>s+6,\qquad f\le N-4,\qquad U(f)\equiv U(N)\equiv s\pmod2
\]

までは得られたが、`s=0,…,20`は一つも落ちなかった。境界`f=N-4`では着地までの符号列が
`−,+,+`に一意化される一方、十分大きい`N`に対し

\[
4N+s\xrightarrow{-(N-3)}3N+s+3
\xrightarrow{+(N-2)}4N+s+1
\xrightarrow{+(N-1)}5N+s
\xrightarrow{+N}6N+s
\]

という一様な抽象suffixが全21本に存在する。必要blockerは`2N+s+5`, `3N+s+2`, `4N+s`で、
legal subtraction生成とforced addition生成の両方を、座標・orbit bound・ledger・parity・freshnessと
両立させられる。同じ構成は任意の`Q≥6`の負potential stripにも拡張できる。不足する条件は、これらの
blockerを実prefixが同時にinstallできるというprovenanceだけである。

評価: 真らしさ **95/100**、独立枝としての証明可能性 **20/100**、A/Bの試験問題として **55/100**。
mod分類による直接攻略は停止し、blocker provenance枝へ統合する。

## D. diagonal predecessor 試験問題

least-tail minimumの唯一の負potential形 `a_n=n` では、full minimum certificateが `n-1` のearly first occurrenceを要求する。

無条件には

\[
n-1\in valuesThrough(n+2)
\]

および

\[
(\exists f<n,\ FirstAt(a,n-1,f))
\lor FirstAt(a,n-1,n+2)
\]

まで既存定理から出る。しかしfull tail hypothesesは前者を排除せず、むしろ選択する。未来も三回のforced additionまでは固定されるが、四回目の候補 `3n+2` はminimumより上で、既存の最小性ではbranchを決定できない。

評価: **35/100**。独立主線ではなく、causal blocker invariantの小さな試験問題とする。一回の追加試行でfull-tail専用の矛盾が出なければ凍結する。

## 更新後の順位

直接証明への寄与と、誤った戦略を止める価値を分けて評価する。

| 枝 | 直接証明 | 戦略価値 | 判定 |
|---|---:|---:|---|
| A. low-quotient tail minimum + ledger | 15 | 85 | canonical high枝が空、直接停止 |
| B. tail interval Hall matching | 25 | 80 | 直接停止、部分定理候補へ移管 |
| C. arbitrary-history countermodel | 20 | 90 | フィルタとして常設 |
| H. `q≥6 → G≥0` | 15 | 80 | 独立枝停止、no-go例として保存 |
| generic blocker provenance | 20 | 70 | noncanonical部分定理として保存 |
| generic blocker fixed budget/reset | 5 | 80 | 棄却済み |
| exact finite extension solver | 20 | 35 | prefix再生になるため停止 |

## 次サイクル

選抜したA/Bの両方が、ロードマップで定めた直接攻略の停止条件に到達した。

1. Aのcanonical high-blocker枝は数値的に空で、一般provenanceは既存history-budget下降へ戻る。
2. Bの`TailHall₃`は非自明な線形成長定理を与えるが、permanent-above性との矛盾機構を持たない。

従って新しい全域性直接サイクルは開始しない。次はLean化済みlow-coordinate/provenance定理、exact Hall probe、
H6・自由履歴no-goを独立成果として整理する。`TailHall₃`は短い局所charging invariantが先に得られた場合だけ
部分定理枠で再開する。全域性直接枝の再開条件は、linear heightとpositive subtraction densityを
permanent-above性に反するものへ変える独立入力、またはold blocker/nonpositive resetを一様排除する定理である。
