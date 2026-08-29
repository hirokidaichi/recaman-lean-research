# Audit

**役割:** 主要な研究定理すべてをLeanカーネルの公理監査 `#print axioms` にかけ、証明が標準基礎以外の公理・未完成証明・ネイティブ評価に依存していないことを機械的に検査する。

## このモジュールの役割

`Audit.lean` は新しい定理を証明するモジュールではなく、プロジェクト全体の**健全性検査**を行うモジュールである。冒頭で `import Recaman`(全モジュールの一括import)を行い、その後は基礎の数列定義から最新の permanent-tail cycle rank まで、研究の主要定理 340 本余りに対して `#print axioms` を1行ずつ実行する。このファイルがエラーなくコンパイルされ、出力に禁止された公理が現れないことをもって、「本リポジトリの定理はすべてLeanカーネルが検査した正真正銘の証明である」ことを保証する。`docs/REPRODUCIBILITY.md` と `scripts/check.sh` が定める検証手順の中核である。

## 監査の仕組み

### `#print axioms` とは

Leanの証明はすべて、最終的に小さな信頼カーネルが型検査する証明項に還元される(いわゆる de Bruijn 基準)。`#print axioms 定理名` は、その定理の証明項が**推移的に**(つまり、使っているすべての補題をたどった先まで含めて)どの公理に依存しているかを列挙するLean標準の検査コマンドである。定理を1本監査すれば、その定理が依存する数百本の補題の依存公理もまとめて検査されることになる。

### 許容される公理と検出したい依存

出力に現れてよいのは、Lean/Mathlibの標準基礎をなす次の3公理だけである。

- `propext` — 命題の外延性(同値な命題は等しい)
- `Classical.choice` — 選択公理
- `Quot.sound` — 商型の健全性

これらは通常の数学(ZFC相当)で普遍的に使われる基礎であり、依存していても定理の価値を損なわない。逆に、次のいずれかが現れたら監査は失敗とみなす。

- `sorryAx` — `sorry` / `admit` で証明を省略した箇所が残っている印。これが無いことは「未完成の証明が一つも混ざっていない」ことを意味する。
- **ユーザー定義の公理** — たとえば全射性やそれに近い命題を `axiom` として仮定してしまえば、いくらでも「証明」できてしまう。そうしたごまかしが無いことを保証する。
- **ネイティブ評価の公理**(`native_decide` 由来の `Lean.ofReduceBool` など) — コンパイル済みバイナリの計算結果を信用する仕組みで、信頼基盤がカーネルの外に広がる。本リポジトリの具体例計算(`Examples.lean`)はすべてカーネル内で完結する `decide` を使い、`native_decide` は使わない。

なお、`CoverageOracle` などの**オラクルを仮定した条件付き定理**(用語集参照)は、仮定を定理の主張の中に明示した含意として書かれている。仮定は公理ではないので `#print axioms` には現れないが、その代わり主張自体を読めば何が仮定されているかが分かる。「隠れた仮定は公理として検出され、明示の仮定は主張に書いてある」という二本立てで、証明の到達点が正確に開示される。

### 二重の防御: `scripts/check.sh`

リポジトリの一括検証スクリプトは、`lake build` と本ファイルの実行(`lake env lean Recaman/Audit.lean`)に加えて、ソース全体を `rg` で走査し `sorry` / `admit` / `native_decide` / `axiom` というトークンの出現自体を禁止する。`#print axioms` による意味論的検査と、字句レベルの検査の二重防御である。

## 監査対象の構成

以下、`#print axioms` の対象をテーマ別に示す。行番号は監査行の開始位置である。

### 数列・履歴の基礎 (L4)

L4〜L7。数列の再帰式 `recurrence`、現在値が履歴に入ること、履歴所属の同値条件、有界範囲での初出時刻 `FirstAt` の存在。すべての解析の土台となる `Basic` / `History` の主定理。

### ゲート・blocker・下降 (L8)

L8〜L20。二連続減算で目標へ着地する完全ゲート `exactGate_sufficient`、blocker(下降を妨げる既出値)証明書から値と初出時刻が下がること、`earlierSmaller` 関係の整礎性、局所脱出のトレース、下降列 `DescentRun` の到達方程式、actual blocker の抽出、目標下降の二分法。

### Coverageオラクルと条件付き全射性 (L21)

L21〜L28。`CoverageStep`(目標出現か、より小さい初出値への一歩)の供給から値に関する強帰納で全射性が従う条件付き定理 `all_coverageOracles_imply_surjective` を含む。大域探索インターフェースの骨格。

### 座標遷移と借り (L29)

L29〜L41。商・剰余座標の通常加減算 `coordinates_add/sub_regular`、借り(法が `n` から `n+1` に変わる際の桁借り)遷移、`BorrowData` の存在・一意性、全域遷移式、複数回借りの算術モデル、最小反例の座標トレース。

### 目標面とチャート (L42)

L42〜L59。ポテンシャル `G(q,r) = r − upperTri(q)` が目標 `m` に一致する目標面と目標方程式の接続、加減算・借り別のチャート(局所座標表)、それぞれから `CoverageStep` を生成する定理、低い商での目標面出現。

### 多段借りの排除と実軌道上界 (L60)

L60〜L77。多段借り(`b ≥ 2`)遷移が負ポテンシャルや目標面と両立しない一連の定理、負領域から非負への横断が一段借りに限ること、実軌道の上界 `a n ≤ upperTri(...)` と `2q ≤ n+1`、そこから実軌道では借りが 0 回か 1 回しか起きないこと(`BorrowData.eq_zero_or_one_of_coordinatesAt`)。

### CoverageStep生成と回復 (L78)

L78〜L110。減算・prestate・一段借り着地から `CoverageStep` を作る各種定理、負領域(ポテンシャルが負の座標領域)の剰余減少、高々 `⌊r/2⌋` 歩で一段借り境界に達すること `eventually_oneBorrow_of_negative_halfRemainder`、負エポックの帰結 `negative_epoch_undershoot_or_coverage`。

### 非負エポックとアンダーシュート (L111)

L111〜L124。非負帯での低商到達またはCoverage、レベル記録、ポテンシャル低下、アンダーシュート帯(`0 ≤ G < m`)の三分岐 `undershoot_epoch_trichotomy`、負・アンダーシュートのサイクル解析。

### 履歴予算・三成分ランク・対角分岐 (L125)

L125〜L150。履歴予算(`missingBelowCount`: 未出の下側値の個数)が初出で真に減ること、履歴予算ランク・三成分履歴探索ランクの整礎性、抽象オラクルからの出現定理、商0・商1の分岐、対角状態(`a t = t` 型)の後方極大減算鎖と早期blockerの抽出。

### 四成分位相探索と負債局所解析 (L151)

L151〜L196。位相探索ランクの整礎性、debt(負債: 通常探索へ戻る前に解消すべき局所的証明義務)への進入・時刻低下・anchor低下による退出、初出遷移の分類、debt中の合法減算・強制加算の分析、debt crossing(target未満から以上への強制横断)が予算を変えないこと、anchor境界の局所形。

### 位相統合とsemantic domain (L197)

L197〜L274。負normal状態の分類、`PhaseSemanticInvariant` への閉包定理群、crossing成長障害の実例、normal invariantの弱さを示す境界反例(`normalSearchInvariant_allows_horizon_value_mismatch` など)、orbit-ready normal 証明書の局所全域ステップ、canonical開始のlevel 0/1/2閉包、typed provenance(生成元証明)による historical normal の処理。

### refined oracleとcrossing境界 (L275)

L275〜L305。extended-history・ready debt・orbit-ready の各分岐から refined step を直接構成する定理、残余が `CrossingSearchInvariant` だけであること、crossing rank 境界(非crossing子は予算の厳密低下が必須)、future downcross による閉包、horizon-below の完全分類と成長残余の実例、tail return 仮説とその全射性との同値 `all_targetTailReturn_iff_surjective`。

### permanent above tailとcycle rank (L306)

L306〜L347。仮想的な最小未出目標が強制する恒久上方tailの内部解析: 高々二遷移のCoverage、zero-budget crossing、tail最小値直下のhistorical blocker、historical反復の有限化、最初のweak upcrossingの存在と一意性、dual budget(`seenBelowCount`)、四成分 permanent-tail cycle rank の整礎性と discharge 退出の必要十分条件まで。研究の現在最前線の定理群である。

## なぜこれで健全性が保証されるのか

保証の論理は次の三段からなる。

1. **コンパイルの成功が定理の存在を保証する。** `Audit.lean` は全モジュールをimportするので、このファイルが通ること自体が、列挙された全定理がカーネル検査を通過して存在していることの証明である。名前の打ち間違いや削除された定理があれば即座にエラーになる。
2. **`#print axioms` が依存の全閉包を開示する。** 各定理について、推移的に使われた公理がすべて列挙される。`sorryAx`・ユーザー公理・ネイティブ評価公理が一つも現れないことを確認すれば、「どこか深部の補題がこっそり `sorry` している」可能性は排除される。
3. **字句検査が抜け道を塞ぐ。** `scripts/check.sh` の `rg` 走査により、監査リストに載っていない補助定義に禁止構文が紛れることも防ぐ。

この構成のもとで信頼すべきものは、Leanカーネルと標準3公理だけに縮む。`experiments/` のC++計算結果は仮説選択のみに使われ、証明の仮定には一切入っていない(この分離も上の検査で機械的に確認できる)。

## 全体の中での位置づけ

`Audit` は `Examples` と並ぶ**検証層**のモジュールであり(証明地図のモジュール層表を参照)、他のモジュールから使われることはない。逆向きに、すべてのモジュールの主定理がここに集約される。証明地図の「証明済み」欄の各項目が本当に証明済みであること、および「未証明」と明示された部分(全域局所被覆と全射性そのもの)以外に隠れた仮定がないことを、読者が `lake env lean Recaman/Audit.lean` の一回の実行で再確認できるようにするのが、このモジュールの存在意義である。
