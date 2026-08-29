# PermanentAboveCorridorCanonicalMinimum

**役割:** tail最小値のwitness時刻という非有界な選択自由度を、tail開始以後の相対的な最初の出現(canonical occurrence)の存在と一意性で除去し、さらにpermanent startとhistorical tail startの二つのcursorを有限keyへ追加した最終的な有限選択stateを構成する。

## このモジュールの役割

exact revisit解析(`PermanentAboveCorridorExactRevisit.lean`)は、finite return枝の再訪を判定する有限key(installed window、down endpoint、historical first time、minimum value)を構成した。しかしdischarge return証明書にはまだ数値的provenanceが残っている。tail最小値を実現する時刻`historicalMinimumTime`は、履歴horizonでは押さえられない(tailの最小値は任意に遅い時刻で実現され得る)ため、これを有限リストへ列挙することはできない。本モジュールの第一の仕事は、この時刻を列挙する代わりにcanonical化することである: tail開始`tailStart`と最小値`a(historicalMinimumTime)`を固定すると、「`tailStart`以後で最初にその値を取る時刻」が存在し、供給された任意のwitness以下であり、しかも一意である。従って同じ`tailStart`と最小値を持つ二つの証明書はwitness時刻が異なっても同一のcanonical時刻に正規化され、最小時刻の選択依存は有限rankではなく恒等性によって消える。第二の仕事は、残る二つの開始cursor(permanent tailの`start`とhistorical tailの`tailStart`)がいずれもparent horizonより厳密に前にあることを示し、これらをexact history keyへ追加した拡張key `TerminalCanonicalTailHistoryKey`の有限列挙と、そこからの消費型選択state(選ぶたびにリストから消して長さが下がる)を構成することである。証明地図の「canonical tail minimum」段階に対応する。

## 主要な定義

### `FirstAtOrAfter` (L21)

下限つき初出。`FirstAtOrAfter seq value start time`は、`start ≤ time`、`seq time = value`、かつ`start`以後に`value`を取るどの時刻`candidate`についても`time ≤ candidate`であること(相対的な最早性)を表す。大域的な初出`FirstAt`の、開始時刻`start`から見た相対版である。

### `CanonicalHistoricalMinimumOccurrence` (L66)

discharge return証明書に対する、historical tail最小値のcanonical化された出現。時刻`time`、値`a(historicalMinimumTime)`の`tailStart`相対初出`first_relative`、および元のwitnessを超えないこと(`time ≤ historicalMinimumTime`)を保持する。

### `TerminalCanonicalTailHistoryKey` (L115)

exact installed history key(`PermanentAboveCorridorExactRevisit.lean`)に、permanent tail開始`permanentStart`とhistorical tail開始`historicalTailStart`の二cursorを追加した拡張key。`DecidableEq`を持つ具体的な数値タプルである。

### `TerminalCanonicalTailHistorySelectionState` (L182)

固定した`target`とhorizonに対する消費型選択state。残余リスト`remaining`と、その全元が有限候補リスト`terminalCanonicalTailHistoryKeys target horizon`に属するという不変条件を持つ。

### `TerminalCanonicalTailHistoryFreshSelectionCertificate` (L228)、`TerminalCanonicalTailHistorySelectionOutcome` (L239)

fresh選択の証明書(候補所属、残余所属、`erase`で得た次state、長さの厳密下降)と、選択の結果型(freshまたはexact revisit: 候補ではあるが残余リストにもう無い)である。

## 定理と証明

### `exists_firstAtOrAfter_bounded` (L29)

**主張:** `seq witness = value`かつ`start ≤ witness`なら、`FirstAtOrAfter seq value start time`かつ`time ≤ witness`なる時刻が存在する。

**証明:** ずらした数列`n ↦ seq(start + n)`を考える。witnessはoffset `witness − start`でこの数列に`value`を与えるので、大域的な初出の存在定理`exists_firstAt`から最小のoffsetを取り、`time = start + offset`と置く。最早性は、`start ≤ candidate`で`seq candidate = value`なるcandidateがもし`time`より前にあれば、そのoffset `candidate − start`が最小offsetより小さくなり矛盾することから従う。`time ≤ witness`は最早性をwitness自身に適用すれば良い。ポイントは、非有界な時刻集合を列挙せず、ずらした数列の大域初出という既存の道具だけでcanonical時刻を構成することである。

### `FirstAtOrAfter.unique` (L56)

**主張:** 同じ数列・値・下限に対する相対初出時刻は一意である。

**証明:** 二つの相対初出は互いに相手の最早性の適用対象になるので、`≤`の反対称性から等しい。

### `PermanentTailDischargeReturnCertificate.exists_canonicalHistoricalMinimum` (L75)

**主張:** すべてのdischarge return証明書はcanonical minimum occurrenceを持つ。

**証明:** 最小値証明書の`minimum.start_le_time`(`tailStart ≤ historicalMinimumTime`)と自明な`a(historicalMinimumTime) = a(historicalMinimumTime)`を、witnessを`historicalMinimumTime`としてL29に渡すだけである。

### `CanonicalHistoricalMinimumOccurrence.time_eq_of_same_tail_value` (L86)

**主張:** 二つのdischarge return証明書(startやparentは異なってよい)が同じ`tailStart`と同じ最小値を持つなら、それぞれのcanonical minimum occurrenceの時刻は等しい。

**証明:** 一方の相対初出を`tail_eq`と`value_eq`で書き換えれば、両者は同じ数列・値・下限の相対初出になり、L56の一意性から時刻が一致する。これが本モジュールの核心である: witness時刻という非有界データの一致を要求する代わりに、有限keyに載る`tailStart`と最小値の一致だけからcanonical時刻の一致が自動的に従う。

### `PermanentTailDischargeReturnCertificate.start_before_parent_horizon` (L101)

**主張:** permanent tailの開始は親のhorizonより厳密に前にある: `start < parent.horizon`。

**証明:** combined証明書のcrossing成分が保持する`tail_strictly_before_horizon`の射影である。

### `PermanentTailDischargeReturnCertificate.tail_start_before_parent_horizon` (L107)

**主張:** historical tailの開始も同様に`tailStart < parent.horizon`。

**証明:** `tailStart ≤ start`(証明書の成分)とL101の合成。この二つの上界により、両cursorは`List.range horizon`で列挙できる有限データになる。

### `terminalCanonicalTailHistoryKeys` (L121)、`mem_terminalCanonicalTailHistoryKeys_iff` (L128)

**主張:** 拡張keyの有限列挙は、exact installed history keysと`List.range horizon`二本の直積(`flatMap`)であり、所属は「history keyの所属 ∧ `permanentStart < horizon` ∧ `historicalTailStart < horizon`」と同値である。

**証明:** `flatMap`と`map`の所属条件を両方向に展開する。逆向きは各成分の所属witnessを順に与える。

### `TerminalFiniteReturnWindowCertificate.canonicalTailHistoryKey` (L160)、`canonicalTailHistoryKey_mem` (L168)

**主張:** finite return window証明書(`PermanentAboveCorridorInstalledStep.lean`)は拡張key `⟨exactHistoryKey, start, tailStart⟩`を定め、そのkeyは`parent.horizon = horizon`の下で有限候補リストに属する。

**証明:** history key部分の所属は既存の`exactHistoryKey_mem`(`PermanentAboveCorridorExactRevisit.lean`)、二cursorの上界はL101とL107をhorizonへ書き換えて適用する。

### `terminalCanonicalTailHistorySelectionProgress_wellFounded` (L200)

**主張:** 選択state間の関係`TerminalCanonicalTailHistorySelectionProgress`(残余リスト長の厳密減少、L195)はwell-foundedである。

**証明:** リスト長という自然数値上の`<`の引き戻しなので、自然数の整礎性から従う。初期state(L188)は全候補リストを残余として持つので、消費は高々`(有限リストの長さ)`回しか起こらない。

### `TerminalCanonicalTailHistorySelectionState.select` (L252)

**主張:** 候補keyと現在のstateが与えられたとき、選択の結果は必ず`TerminalCanonicalTailHistorySelectionOutcome`のいずれかである: keyがまだ残余にあればfresh(erase後のstateと長さの厳密下降つき)、無ければexact revisit。

**証明:** 残余への所属で場合分けする。fresh側では`List.length_erase_of_mem`により、erase後の長さが元の長さから1減ることを確かめて証明書(L228)を組む。`erase`(L217)は残余の不変条件(全元が候補リストに属する)を`List.mem_of_mem_erase`で保存する。

### `TerminalFiniteReturnWindowCertificate.canonicalTailHistorySelection` (L273)

**主張:** finite return window証明書は、自分のcanonical tail history keyを現在のstateに対して直接選択できる。

**証明:** L160のkeyとL168の所属をL252に渡す適配定義である。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「canonical tail minimum」(start差を有限化・minimum時刻を一意化済み)に対応する。入力は`PermanentAboveCorridorExactRevisit.lean`の有限history keyと、`PermanentAboveTail.lean`のtail最小値証明書である。出力は二系統ある。第一に、canonical minimum occurrenceの存在と一意性(L75、L86)は、有限keyに最小値のwitness時刻を含めなくても再訪判定が意味を持つことを保証する。第二に、拡張keyの選択state・fresh証明書・選択outcomeは、`PermanentAboveCorridorCanonicalStateStep.lean`がterminal総合outcomeへstateをthreadする際の直接の部品となり、さらに`PermanentAboveCorridorReplayBoundary.lean`がこの選択機構の限界(key全消費後のexact revisit)を形式化する土台になる。
