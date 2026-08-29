# CrossingReadinessClosure

**役割:** readiness橋の監査述語を定理に格上げして橋の全結論を無仮定化し、大域残余を`TargetTailReturnHypothesis`一本へ純化する。ただしその一本はtargetの出現と論理的に同値であり、難しさは減っていない。

## このモジュールの役割

`CrossingReadinessBridge.lean`は、unready crossing漏れを二つの入力へ縮約した。ひとつは監査述語`OrbitReadyNormalNonCrossingStep`（orbit-ready normal親の子は決してcrossing構成子に落ちない、という「既存定理が記録し忘れていた事実」）、もうひとつは`ReadyCrossingReadyStepHypothesis`（ready crossing節点からclockを保つ子への局所step）である。前者は`OrbitReadyDirectRefined.lean`側の内部ヘルパー群の結論を非crossingの連言へ強化することで**証明済みの定理**になった。本モジュールはその事実を受け取り、橋の全結論から監査述語を消す。

その結果、大域残余は`0 < target ∧ TargetTailReturnHypothesis target ⟹ ∃ t, a t = target`という一本の含意になる。refined再帰・horizon clock・crossing-recovery構成子はすべて解消されている。

**ただし本モジュールは同時に`targetTailReturn_iff_occurs`を証明しており、残った仮定はtargetの出現と論理的に同値である。** つまり「残余が一本に縮約された」という記述は足場の量についてのみ正しく、証明の困難さについては何も言っていない。減ったのは足場であって難しさではない。このモジュールは前進の記録であると同時に、その前進の正確な価格の記録でもある。

## 定理と証明

### `orbitReadyNormalNonCrossingStep` (L23)

**主張:** 監査述語`OrbitReadyNormalNonCrossingStep target`は、任意の`target`について定理である。すなわち、orbit-ready normal節点は常に、targetを出現させるか、**非crossing**のrefined子（ready current/debt または extended-history）へrank下降する。

**証明:** `OrbitReadyDirectRefined.lean`の`OrbitReadyNormalInvariant.nonCrossingRefinedStep`をそのまま受ける。以前この生成器は結論をrefined union（ready current/debt ∨ extended-history ∨ crossing recovery）で述べていたため、目視監査では全分岐が非crossingへ落ちることが分かっていながら型がそれを記録していなかった。生成器側の内部ヘルパー8本の結論を非crossingの連言へ強化することで欠けていた情報が復元され、証明本体はほぼ変わらないまま（実質的な変更は4箇所）statementだけが強くなった。

**この定理の意味:** 「証明できていなかったこと」が新たに証明されたのではなく、「証明の中に既にあったが型に載っていなかったこと」が型に載った。橋の側にとっては仮定が一本消えたことに変わりはないが、数学的な内容が増えたわけではない。

### `ReadyRefinedInvariant.closedStep` (L35)

**主張:** `0 < target`のもとで、ready refined節点は、targetを出現させるか、ready refined子へrank下降する。残る入力はclock保存crossing stepだけである。

**証明:** 橋の`ReadyRefinedInvariant.readyStep`にL23を代入する。

### `closedReadyRefinedPhaseSearchOracle` (L46)

**主張:** clock保存crossing stepを認めれば、horizon-ready refined domainは制限付きphase-searchオラクル（四成分lex rankの下降を保証する局所全域な子供供給器）である。

**証明:** 橋の`readyRefinedPhaseSearchOracle`にL23を代入する。

### `readyCrossingReadyStepHypothesis_implies_occurs` (L55)

**主張:** `0 < target`と`ReadyCrossingReadyStepHypothesis target`から`∃ t, a t = target`。

**証明:** canonical startから上のオラクルで整礎下降する（橋の`occurs_of_readyCrossingReadyStep`にL23を代入）。

### `readyCrossingReadyStepHypothesis_iff_occurs` (L63)

**主張:** `0 < target`のもとで`ReadyCrossingReadyStepHypothesis target ↔ ∃ t, a t = target`。

**証明:** 順方向はL55。逆方向は、targetが出現するならどの節点でも第一枝を返せばよい。

**この定理の役割:** 残ったcrossing局所stepの**正確な値段**を述べている。仮説は結論と同値なので、これを「あと一歩」と読んではいけない。橋が達成したのは仮説の適用範囲の縮小（全crossing節点上の素の`CrossingRefinedStepHypothesis` → ready crossing節点上でready子を返すstep）であって、仮説の強さの緩和ではない。

### `phaseSemanticChild_occurs_of_readyCrossingStep` (L72)

**主張:** horizon-readyなsemantic子から始めた下降でも、clock保存crossing stepだけで出現が出る。

**証明:** 橋の対応する定理にL23を代入する。

### `targetTailReturn_implies_occurs` (L89)

**主張:** `0 < target`と`TargetTailReturnHypothesis target`（target以上の値を取る任意の時刻以降に、targetが出現するかtarget未満へ戻る時刻が存在する）から`∃ t, a t = target`。

**証明:** tail returnからready crossing用のtail downcross形を作り、それがclock保存crossing stepを供給する（橋の`occurs_of_targetTailReturn`）。あとはL23を代入する。

これが現時点での**大域残余の headline 形**である。仮定は軌道についての単一の長期命題ひとつであり、探索木の構造・horizon時計・crossing recovery構成子はもう表に出ない。

### `targetTailReturn_iff_occurs` (L98)

**主張:** `0 < target`のもとで`TargetTailReturnHypothesis target ↔ ∃ t, a t = target`。

**証明:** 順方向はL89。逆方向は、targetが出現するなら任意の`start`に対して第一枝を返せばよい（tail return の定義が出現を選択肢に含んでいるため、これは自明である）。

**この定理が本モジュールで最も重要である。** 残った唯一の仮定は、証明したい結論そのものと同値である。従って次のような読み方は誤りである——「あとはtail returnという軌道の性質を示せばよい」。tail returnを示すことはtargetの出現を示すことと同じ難しさであり、縮約によって作業量が実質的に減ったわけではない。**減ったのは足場の量であり、難しさは減っていない。** 縮約の価値は、今後の攻撃が「探索木の構成子や時計条件の整合性」ではなく「軌道の長期挙動」という単一の対象へ集中できる点にあり、それ以上ではない。

同種の指摘は本プロジェクトの他所にもある。`SemanticOracleRecursion.lean`の`semanticBranchClosure_iff_occurs`はsemantic枝の閉包が出現と同値であることを述べ、`CrossingReadinessBridge.lean`の`readyCrossingReadyStep_iff_occurs`と`LeastMissingTarget.not_readyStep_pair`はcrossing側について同じ役割を果たす。これらは前進を打ち消す指摘ではなく、**前進の大きさを誤読させないための装置**である。

### `surjective_of_targetTailReturn` (L111)

**主張:** すべての`target`で`TargetTailReturnHypothesis target`が成り立つなら、Recamán列は全射である。

**証明:** `target = 0`は`a 0 = 0`。正の`target`はL89を直接適用する。

**既存版との差:** `CrossingTailRefined.lean`の`all_targetTailReturn_implies_surjective`は同じ結論を、強帰納法で最小未出target（`LeastMissingTarget`）を作り`LeastMissingTarget.not_targetTailReturn`で矛盾させる背理法として得ていた。本版は各targetを**それ自身のrefined再帰だけ**で閉じるので、強帰納も最小反例への迂回も要らない。ただしこれは証明の構造の改善であって、含意の強さは同じである。実際`all_targetTailReturn_iff_surjective`が既に示すとおり、tail return仮説の族は全射性予想と同値であり、本定理はその同値の片方向を別ルートで再証明したものにすぎない。

## 全体の中での位置づけ

証明地図（docs/PROOF_MAP.md）の「大域残余」行に対応し、そこには「仮定一本へ純化済み。ただし同仮定は出現と同値なので難しさは移動しただけ」と記録されている。上流は`CrossingReadinessBridge.lean`（readiness橋本体）と`OrbitReadyDirectRefined.lean`（監査述語の内容を供給する`nonCrossingRefinedStep`）である。

このモジュールで、探索側の縮約は一段落する。canonical startからready refined domain上を四成分lex rankで下降する再帰は、`TargetTailReturnHypothesis`ひとつを除いて完全に無仮定で動く。逆に言えば、探索木の設計をこれ以上精密化しても残余は動かない。次に必要なのは軌道の長期挙動そのものについての新しい情報であり、それは`PermanentAboveCorridor*`系（仮想反例のpermanent tailを数値的に挟み撃つ路線）や`PinnedConfigurationAttack`（残余配置の構造的決着）が担当している。
