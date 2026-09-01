# TargetStreamBlockerUnbounded

**役割:** unbounded right-terminal stream内の全terminal blockerが分離root以上であること(blocker床)と、blockerとentryが任意の天井を超えること(非有界性)を、時系列chain構成とone-use鳩の巣で示す。

## このモジュールの役割

`TargetTailResidualKernel.lean` のB枝は、tail内の全完了comb(櫛状区間)のentryを固定の分離root以上に保つunbounded right-terminal streamである。本モジュールはこのstreamから二つの定量的帰結を取り出す。第一に、entryの床をblocker(妨害値)の床へ持ち上げる: streamの真内部の全combは `root ≤ blocker` を満たす。第二に、streamは時系列的に非有界なので、互いに交わらない完了combの選択列(chain)を取り出せる。相異なる最終時刻は相異なるblockerを強制するので、有限鳩の巣によりblockerは任意の天井 `B` を超え、entryはそれよりさらに大きい。すなわちstreamのblockerとentryは、分離rootの右側に留まったまま、どの固定天井からも逃げ出す。

## 定理と証明

用語を確認する。comb `HistoryTerminatedComb s k blocker` は時刻 `s` にfresh値 `a s` で始まり「強制加算+即時返済減算」を `k` 周期続けて時刻 `s + 2k` に着地する区間で、low rail `a (s + 2i) = a s − i` はすべて初出、最終着地は `a (s + 2k) = blocker + 1`、返済候補 `blocker` が既出のため停止する。entry恒等式 `a s = blocker + k + 1` が成り立つ。減算候補は `nextSubtractionCandidate n = a n − (n + 1)` であり、これがtarget未満のcombをtarget-lowと呼ぶ。stream `UnboundedRightTerminalStream target tailStart root` は (i) tail内の全完了combについて `root ≤ a start`(no-escape床)、(ii) 任意のcutoffより後に開始するtarget-lowの完了combの存在、の二成分である。

### `UnboundedRightTerminalStream.blocker_floor` (L28)

**主張:** streamと、`rootFirstTime ≤ tailStart` を満たすrootの初出証明 `FirstAt a root rootFirstTime` のもとで、tailの真内部(`tailStart < start`)の任意の完了comb `HistoryTerminatedComb start length blocker` について `root ≤ blocker` が成り立つ。

**証明:** streamの成分(i)よりentry床 `root ≤ a start` を得る。また `rootFirstTime ≤ tailStart < start` よりrootの初出はcombの開始より真に前である。ここで `TargetCombSemanticMount.lean` のanchor補題 `entry_below_or_anchor_le_blocker` を `anchor = root` に適用する: combの開始より前に初出した任意の値anchorについて

`a start < anchor`　または　`anchor ≤ blocker`

が成り立つ。理由は区間packingと同じである。仮に `blocker < anchor ≤ a start` とすると、combのlow railは `a start` から `blocker + 1` まで1ずつ降りるから、`i = a start − anchor ≤ length` として時刻 `start + 2i` で値anchorをちょうど踏む。しかしlow railの各値はその時刻での初出であり、anchorはすでに `firstTime < start` で出現している。矛盾。従ってfresh区間は既出のanchorを跨げない。

第一枝 `a start < root` はentry床と矛盾するので、第二枝 `root ≤ blocker` が残る。∎

### 補助構成: `streamPick` と `streamChain` (L49)

以下はすべてprivateな補助構成であり、まとめて述べる。`exists_lowCombTriple` (L49) はstreamの成分(ii)を「開始・長さ・blockerの三つ組」の存在命題に詰め直したものである。`streamPick` (L67) は各cutoffに対しその三つ組を `Classical.choose` で一つ選ぶ選択関数で、`streamPick_spec` (L74) がその定義的性質(cutoff超・tail真内部・target-low・完了comb)を与える。`streamChain` (L87) は時系列chainを再帰的に構成する: 第0 linkは `streamPick` をcutoff `tailStart` で呼び、第 `i+1` linkは第 `i` linkの最終時刻 `startᵢ + 2·lengthᵢ` をcutoffにして次のcombを選ぶ。`streamChain_spec` (L98) と射影 `streamChain_tail` (L124)・`streamChain_low` (L132)・`streamChain_comb` (L140) により、各linkはtail真内部のtarget-low完了combである。`streamChain_final_lt_succ` (L149) は、`startᵢ₊₁` が `finalᵢ = startᵢ + 2·lengthᵢ` より真に後で、かつ `finalᵢ₊₁ ≥ startᵢ₊₁` であることから、隣接linkの最終時刻が厳密に増加することを示す。`streamChain_final_lt_of_lt` (L166) はこれを `i < j` 一般に延ばした狭義単調性、`streamChain_final_injective` (L187) はその帰結としてchainの最終時刻がlinkの添字を決定する(単射である)ことを示す。

### `UnboundedRightTerminalStream.exists_blocker_gt` (L205)

**主張:** 任意の天井 `B` に対し、tail真内部・target-lowの完了comb `HistoryTerminatedComb start length blocker` で `B < blocker` を満たすものが存在する。

**証明:** chainの最初の `B + 2` 本のlinkを取る。前段の単射性により、それらの最終時刻は互いに相異なる。ここに `TargetCombFiniteCeiling.lean` のone-use鳩の巣 `exists_blocker_gt_of_many` (L51) を適用する:

> 最終時刻が互いに相異なる `B + 2` 個の完了combのうち、少なくとも一つはblockerが `B` を超える。

この鳩の巣の理由は次のとおりである。すべてのblockerが `B` 以下と仮定する。同じblocker値を持つ二つの完了combは最終時刻が一致する(`same_blocker_finalTime_eq`)。実際、最終着地値 `blocker + 1` はその時刻での初出であり、初出時刻は値ごとに一意だからである。つまり各blocker値は高々一つの最終時刻でしか「使え」ない(one-use性)。従ってblockerの割当は単射になり、`B + 2` 個の相異なる自然数が `{0, 1, …, B}` の `B + 1` 個の値に収まることになって矛盾する。

得られたlinkはchainの性質によりtail真内部かつtarget-lowなので、そのまま結論の証人になる。∎

### `UnboundedRightTerminalStream.exists_entry_gt` (L235)

**主張:** combのentryも任意の天井を超える: 任意の `B` に対し、tail真内部の完了combで `B < a start` を満たすものが存在する。

**証明:** `exists_blocker_gt` で `B < blocker` のcombを取り、entry恒等式 `a start = blocker + length + 1 > blocker > B` を読むだけである。∎

### `UnboundedRightTerminalStream.blockers_escape_every_ceiling` (L251)

**主張:** kernel向けの束ね形。rootの初出証明(`rootFirstTime ≤ tailStart`)付きのstreamでは、任意の `B` に対し、tail真内部・target-lowの完了combで `root ≤ blocker` かつ `B < blocker` を**同時に**満たすものが存在する。

**証明:** `exists_blocker_gt` の証人に `blocker_floor` を適用して床を付け加える。∎

## 全体の中での位置づけ

Round 16の6-gate分解のうちGate 3〜4(区間packing → blocker非有界)を完全にLean化したモジュールである。`blocker_floor` と `exists_blocker_gt` は `SharpResidualKernel.lean` の `SharpResetStream` のフィールド `blocker_floor`・`blockers_unbounded` にそのまま供給され、両者の合成は同モジュールの `exists_blocker_in_band` として再輸出される。姉妹モジュール `TargetStreamUpwardResets.lean`(Gate 5: 無限upward reset)とあわせて、B枝の残余はreset repayment予想(docs/RESET_REPAYMENT_AUDIT_2026-09-01.md で `STOPPED`)にexactに絞られた。証明地図では docs/PROOF_MAP.md の「2026-09-01 午後: sharp residual kernel(A/B両枝の並列精密化)」のB枝に対応する。
