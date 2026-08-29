# PermanentAboveCorridorReplayPinning

**役割:** exact replay固定点の三等式(anchor再生・crossing時刻一致・eligibility)から`returnTime = oldCrossingTime = crossingTime`というcycleの文字どおりの閉包を導き、その数値的帰結を列挙する。さらにinstalled nodeがparentそのものであることを示し、replayをrank-levelだけでなくnode-levelのself-map固定点として固定する。

## このモジュールの役割

`PermanentAboveCorridorIterationClosure.lean`が残した唯一の非進捗形はexact replay証明書である。この証明書は三つの等式・不等式を保持している: installed anchorがparent anchorに等しい(`a(crossingTime) = parent.anchorParent`)、選択crossing時刻がold crossing時刻に等しい(`crossingTime = oldCrossingTime`)、そしてold crossingがfresh downcross endpointからchronologically eligible(`downTime + 1 ≤ oldCrossingTime`)であること。本モジュールは、これらと選択時の上界(`crossingTime ≤ returnTime ≤ oldCrossingTime`)を組み合わせると、canonical return自体がold crossingの上に乗ること、すなわちdischargeが「endpoint → return = old crossing」という文字どおりのcycleを閉じることを導く。そこから、crossing clockがcrossing値より厳密に小さいこと、terminal blockerの初出がcrossingより厳密に前にあること、crossing stepがtargetをまたぐ明示的なforced additionであること、といった数値的帰結が芋づる式に得られる。最後に、ready crossing nodeはhorizonとanchorで一意に決まるため、installed node は数値的にparentそのものであり、successor dischargeは同じparent・同じold crossing cursorへtransportされる。replayは真の自己写像の固定点である。

## 定理と証明

### `PermanentTailDischargeReturnCertificate.exists_transport_of_node_eq` (L28)

**主張:** discharge証明書はparent nodeの等式に沿って、old crossing cursorを動かさずに輸送できる。

**証明:** 等式`nodeA = nodeB`をcasesで潰せば型が一致し、同じ証明書がそのままwitnessになる。補助補題である。

### `return_eq_oldCrossingTime` (L43)

**主張:** exact replayではcanonical return時刻はold crossing時刻に等しい。

**証明:** eligibilityにdischarge証明書の`returnTime_le_oldCrossingTime`を適用して`returnTime ≤ oldCrossingTime`。一方、選択crossingのcanonical性から`crossingTime ≤ returnTime`であり、replayの`time_eq`は`crossingTime = oldCrossingTime`。三つを算術的に挟めば等号になる。

### `return_eq_crossingTime` (L52)

**主張:** 同値な形として、return時刻は選択crossing時刻そのものである。

**証明:** L43と同じ三つの事実からの算術。

### `endpoint_le_crossingTime` (L61)

**主張:** fresh downcross endpointは選択crossing以前にある: `downTime + 1 ≤ crossingTime`。

**証明:** eligibilityと`time_eq`の書き換え。

### `canonicalReturn_is_oldCrossing` (L70)

**主張:** cycleの閉包。fresh downcross endpointからのcanonical first upcrossingは、まさにold crossingである: `FirstWeakUpcrossingStep target (downTime + 1) oldCrossingTime`。

**証明:** discharge証明書が保持するreturn時のfirst upcrossingを、L43の等式で書き換えるだけである。以後の議論でこの「最初性」が強力な武器になる(後続モジュールのcorridor band証明が典型)。

### `firstTime_lt_crossingTime` (L78)

**主張:** terminal blockerの初出はcrossingより厳密に前にある。

**証明:** blockerの`firstTime < returnTime`とL52の書き換え。

### `clock_lt_crossingValue` (L86)

**主張:** replay crossingの値は自分のclockより厳密に大きい: `crossingTime + 1 < a(crossingTime)`。

**証明:** blockerのcandidateは`a(returnTime) − (returnTime + 1)`と定義されており(`candidate_eq`)、L52でreturnをcrossingに書き換えると`candidate = a(crossingTime) − (crossingTime + 1)`。candidateは正(`candidate_positive`)なので、引き算が自然数で正になるためには`crossingTime + 1 < a(crossingTime)`が必要である。

### `candidate_eq_at_crossing` (L97)

**主張:** blocker candidateはcrossing clockでのexactな減算欠損`a(crossingTime) − (crossingTime + 1)`である。

**証明:** `candidate_eq`のL52による書き換え。

### `forced_addition_at_crossing` (L106)

**主張:** crossing stepは明示的な強制加算である: `a(crossingTime + 1) = a(crossingTime) + (crossingTime + 1)`。

**証明:** discharge証明書のold crossing(weak upcrossing)は減算不能性を保持している。`time_eq`でold crossing時刻をcrossing時刻に書き換え、`a_succ_of_not_canSubtract`で漸化式の加算枝を取り出す。

### `crossing_straddles_target` (L114)

**主張:** crossingはtargetをまたぐ: `a(crossingTime) < target ≤ a(crossingTime + 1)`。

**証明:** 下側は選択crossing証明書のfirst crossingの`below`。上側はold crossingの`endpoint_ge`を`time_eq`で書き換える。

### `installed_node_eq` (L123)

**主張:** node-levelの固定点。ready crossing nodeはそのhorizonとanchorで決まるので、installed node `terminalPredecessorCrossingNode parent crossingTime`は文字どおりparentである。

**証明:** parentのready crossing証明書を展開すると、その`node_eq`によりparentは`⟨horizon, a(oldTime), normal, a(oldTime)⟩`の形で、特に`parent.anchorParent = a(oldTime)`。installed nodeは定義から`⟨parent.horizon, a(crossingTime), normal, a(crossingTime)⟩`であり、replayの`anchor_eq`(`a(crossingTime) = parent.anchorParent`)で書き換えると両者の全成分が一致する。

### `exists_nextOnParent` (L137)

**主張:** successor dischargeはまさに同じparent nodeの上へ、同じold crossing cursorとともにtransportされる: `∃ next : PermanentTailDischargeReturnCertificate target start parent, next.oldCrossingTime = source.oldCrossingTime`。

**証明:** replayが保持する次discharge `next.discharge`(parentはinstalled node)を、L123のnode等式に沿ってL28で輸送する。輸送はold crossing cursorを保つので、`next.old_crossing_time_eq`(installされた次dischargeのold crossingは選択crossing時刻)と`time_eq`から、cursorは`source.oldCrossingTime`のまま変わらない。すなわちreplayは「rankが動かない」だけでなく、「解析対象のnodeとcursorそのものが再帰の一周で完全に再現される」自己写像の固定点である。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「exact replay pinning(固定点をnode-level cycleへ固定済み)」に対応する。上流は`PermanentAboveCorridorIterationClosure.lean`(replay枝の分離)と`PermanentAboveCorridorSelectedInstall.lean`(installと次dischargeの構成)である。ここで得た等式群、とりわけ`canonicalReturn_is_oldCrossing`(cycle閉包)、`clock_lt_crossingValue`(clock対値の不等式)、`crossing_straddles_target`(target跨ぎ)は、`PermanentAboveCorridorReplayCorridor.lean`が全cursorをtarget未満の初期帯へ押し込み、`PermanentAboveCorridorReplayFloor.lean`がkernel計算でclockとtargetの下限を引き上げる際の、直接の入力になる。replayが「任意の抽象的な停留」ではなく「軌道上の一つの具体的なcycleの再生」であることを確定させた点が、この固定点を数値攻撃可能にした転回点である。
