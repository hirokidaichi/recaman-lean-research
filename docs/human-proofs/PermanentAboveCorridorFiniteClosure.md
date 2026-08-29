# PermanentAboveCorridorFiniteClosure

**役割:** finite insufficient窓が実は不可能であることを算術的に証明する。最終強制加算とinsufficient上界からendpoint値が1以下に押さえられ、`endpoint = 1`、`returnTime = 2`、targetは4または5に限定されるが、いずれも実軌道に出現する(`a(131) = 4`、`a(129) = 5`)ためmissing-target仮定と矛盾する。これによりterminal outcomeから数値枝が完全に消え、replay resolverも無条件に成立する。

## このモジュールの役割

terminal residual treeで最後まで残っていた数値枝は、all-forced suffixの有限窓`TerminalFiniteReturnWindowCertificate`(`endpoint < return < target < 2(return+1)`のclock band、加算trace、最終減算失敗のinsufficient証明書を束ねた証明書)だった。先行モジュール群はこの枝を有限選択rankとexact revisit解析で囲い込み、`PermanentAboveCorridorReplayBoundary.lean`は残る義務を一つのresolver命題に限定した。本モジュールはその枝自体をFalseへ落とす。鍵となる観察は、insufficient上界`a(return) ≤ return + 1`を最終内部強制stepの方程式に代入すると直前値が高々1になり、all-forced traceがこの上界をfresh endpointまで逆向きに輸送することである。endpointは正時刻での値の初出なので、値も時刻も1に確定し、suffixがそれ以上長ければ最初のclockだけで上界を破るため`return = 2`に確定する。すると横断は実値`a(2) = 3`と`a(3) = 6`の間で起こり、targetは4か5しかないが、両方とも実軌道に既出である。仮定を追加せずに、exact replayを含むfinite枝全体が消える。

## 主要な定義

### `PermanentTailTerminalFiniteClosedOutcome` (L150)

不可能になったfinite枝を除去したterminal分類。`history_progress`(`missingBelowCount`のstrict下降)、`immediate_semantic`(即時谷のsemantic閉包、`PermanentAboveCorridorImmediateClosure.lean`)、`historical_complete`(complete historical predecessor step、`PermanentAboveCorridorAboveClosure.lean`)の三constructorのみを持つ。

## 定理と証明

### `forcedClockSum_firstClock_le` (L23)

**主張:** 少なくとも1歩ある強制加算runのclock総和は最初のclock以上: `0 < steps`なら`start + 1 ≤ forcedClockSum start steps`。

**証明:** `forcedClockSum start (steps+1) = forcedClockSum start steps + (start + steps + 1)`を一段展開すれば線形算術で従う。

### `TerminalFiniteReturnWindowCertificate.endpoint_return_eq` (L33)

**主張:** insufficientなall-forced窓は最初の小さな形しか持たない: `terminalEndpoint = 1`かつ`source.returnTime = 2`。

**証明:** `lastTime = returnTime − 1`とおく。endpointはdowncross endpoint(時刻`downTime + 1 ≥ 1`)以後なので正であり、窓の`endpoint_before_return`から`terminalEndpoint ≤ lastTime < returnTime`。

*直前値の上界。* 時刻`lastTime`の内部stepは全強制条件により強制加算なので`a(returnTime) = a(lastTime) + returnTime`。一方insufficient証明書の`predecessor_le_clock`は`a(returnTime) ≤ returnTime + 1`。両者から`a(lastTime) ≤ 1`。

*endpointへの輸送。* all-forced traceのtelescoping式(`value_eq_add_forcedClockSum`、`PermanentAboveCorridorRank.lean`)により`a(lastTime) = a(terminalEndpoint) + forcedClockSum(terminalEndpoint, lastTime − terminalEndpoint)`。clock総和は非負なので`a(terminalEndpoint) ≤ 1`。

*endpointの値と時刻の確定。* endpointは正時刻での値`a(terminalEndpoint)`の初出である(suffixの`endpoint_first`)。もし値が0なら`a(0) = 0`が時刻0での同じ値の出現となり初出性に反するので、`a(terminalEndpoint) = 1`。さらに`terminalEndpoint > 1`なら`a(1) = 1`(カーネル計算)が時刻1での同じ値の先行出現となりやはり初出性に反する。よって`terminalEndpoint = 1`。

*returnの確定。* もし`returnTime > 2`なら`lastTime ≥ 2 > 1 = terminalEndpoint`なのでtraceは少なくとも1歩を含み、L23により`forcedClockSum ≥ terminalEndpoint + 1 = 2`。すると`a(lastTime) ≥ 1 + 2 = 3`となり上界`a(lastTime) ≤ 1`に反する。`endpoint < return`とあわせて`returnTime = 2`。

### `TerminalFiniteReturnWindowCertificate.target_eq_four_or_five` (L100)

**主張:** finite窓のtargetは4または5に限る。

**証明:** L33で`returnTime = 2`。窓のstrict crossing条件`a(returnTime) < target < a(returnTime + 1)`に、カーネルの`decide`で検証した実値`a(2) = 3`、`a(3) = 6`を代入すると`3 < target < 6`。targetは整数なので4か5である。

### `TerminalFiniteReturnWindowCertificate.target_occurs` (L119)

**主張:** 算術的に可能な両targetは、いずれも実軌道に出現する: `∃ witness, a(witness) = target`。

**証明:** `target = 4`なら`a(131) = 4`、`target = 5`なら`a(129) = 5`。どちらもLeanカーネルの`decide`(再帰深度上限を引き上げて実行)による有限計算の検証であり、外部計算結果を公理として仮定してはいない。

### `TerminalFiniteReturnWindowCertificate.false` (L135)

**主張:** missing permanent-tail反例の下ではfinite insufficient terminal証明書は存在できない: 任意の`TerminalFiniteReturnWindowCertificate`から`False`が従う。

**証明:** 窓が保持するmissing-target条件(`target_missing : ¬∃ witness, a(witness) = target`)がL119の出現witnessと直接矛盾する。

### `terminalExactCanonicalReplayResolver` (L144)

**主張:** `PermanentAboveCorridorReplayBoundary.lean`で「最小の未解決数学的義務」として切り出されたreplay resolver命題`TerminalExactCanonicalReplayResolver target`は、すべてのtargetについて無条件に成り立つ。

**証明:** resolverの仮定にはfinite証明書が含まれるが、L135によりそれはFalseなので、結論は空虚に成立する。開いていた条件付き閉包が無条件になった。

### `PermanentTailDischargeReturnCertificate.terminalFiniteClosedOutcome` (L174)

**主張:** すべてのdischarge/return証明書は、数値枝を持たない`PermanentTailTerminalFiniteClosedOutcome`を持つ。

**証明:** `terminalSemanticallyClosedOutcome`を場合分けし、`finite_return_candidate`枝はL135の`False`で消去、他の三枝はそのまま写す。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「finite window closure」(finite numeric枝を完全排除済み)に対応する。上流は`PermanentAboveCorridorReplayBoundary.lean`(resolver命題の切り出し)、`PermanentAboveCorridorInstalledStep.lean`(full finite window証明書)、`PermanentAboveCorridorWindow.lean`/`Rank.lean`(all-forced traceとclock sum)、そして`Basic.lean`の実行可能定義に基づくカーネル計算である。この結果により、return/window/installed selectionからexact revisitに至る有限選択の塔は「対象が空である」ことの証明で頂点に達し、visited rankやreplay resolverを外側の反復rankへ組み込む必要自体が消えた。下流では`PermanentAboveCorridorTerminalProgress.lean`がfinite-freeになったoutcomeを四つのprogress形(target出現・strict history・semantic phase・installed master)へ平坦化し、`PermanentAboveCorridorTerminalSuccessor.lean`がinstalled master枝の反復provenanceを接続する。
