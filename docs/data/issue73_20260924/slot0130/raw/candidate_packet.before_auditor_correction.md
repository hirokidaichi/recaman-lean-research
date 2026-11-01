# 2026-09-24 01:30 週間後半候補・反例・停止 packet

## 結論（独立合同監査待ち）

週報は、H-02/H-03/H-05の**限定意味監査合格**と各カードの**総合手続き未完了**を分ければ、
既存証拠を過大評価せず記述できる。三者は `CONJECTURED` のままで、新規登録・昇格・確立済みの
後続根拠への採用はできない。H-04は、監査済みの一つのp16 literalが反証する
**非最小lag15 donor延長だけ**を `REFUTED`、同一ルートを `STOPPED` と書ける。

このpacketは既存証拠の週間整理で、新しい数学、範囲延長、Lean定理、証拠登録・昇格、status変更ではない。
週報・4カードへの適用は、別Solによる合同監査と親の承認後に限る。予定される正本監査は
[`docs/adversarial_audits/H-20260920-02_20260924_0130.md`](../../../adversarial_audits/H-20260920-02_20260924_0130.md)。

## 凍結した一問・合格条件・停止条件

- 問い: H-02/H-03/H-05の限定合格とH-04の反例・停止について、一般p、一般lag、実軌道を混同せず、
  週報がどこまで言えるか。
- 合格条件: 各主張のexact quantifiers、全仮定、結論、依存、反例・非空例、未監査範囲、履歴的入口欠落を
  source、9/23監査、原archiveへ追跡でき、限定意味合格を総合合格と書かないこと。
- 停止条件: 新しい数学入力なしでは一般lagへ進めないと明記し、01:48までに草稿を凍結する。
  source/定義/根拠に不一致があれば適用せず未完了として戻す。

## 主張台帳

### H-20260920-02: lag11 donor、donor最小性を仮定しない

- exact domain: 任意 `e : Int -> Bool`、任意 `p : Nat`、`0<p`、周期性、nodup `B`、tightness、
  `b<p`、current A、各memberのlagが3/7/11、その窓がP2かつ最小。任意 `u0 : Int` の長さ11窓が
  P2かつSS=2。
- 結論: donorの**真の**最古S phaseは `neighborhood e p B lag` に入らない。
- 明示的に不要: donor最小性、donor current-A、donorのB外所属、ambient U/Hall、正period mass、p上限。
- 依存: short-window Hall、tight owner-family lift、E-357のlag11/w2 member排除、E-360に既存の
  `w1_future_aas_member`。E-351のnext-A仮定を逆向きに使わない。
- 非空例: p13 `AASSSAAAASSSS`, `u0=10`, donor `SAAAASSSAAS`, proper P2 prefix7、current S、
  `B=[7]`, `N=[4]`, true offset11・phase12。これは反例ではなく前件の実在確認。
- 判定: theoremの限定意味監査は合格。昼の独立preformalization entry review欠落により総合**未完了**、
  `CONJECTURED`。最初の二つの失敗checker runの実行時source/hashも欠落。
- 禁止拡張: 一般lag、lag15以上、一般Gate T6、full all-lag U、実軌道。

### H-20260920-03: short prefix neighborhood equality

- exact Lean domain: 任意の正周期pと周期符号語e、nodup・範囲内current-AのB、
  `m b <= lag b <= 11`、m側窓P2、lag側の `|N_lag(B)|=|B|`。
- 結論: `N_m(B)=N_lag(B)`。
- 元カードとの差: 元カードはlag側full-window P2とmの最小性も要求する。Lean文は要求しないため広い。
  元カードからLean文へは `exists_minimal_p2_prefix` で進めるが、逆向きは不可。
- 非空・境界: p4 `AAAS`, `B=[2]`, `m=lag=3` は元カードの同一長非空例。
  p4の `m=3,lag=4` はLean文のstrict/tight例だがlag4窓はP2でない。
  p9 `ASAAASASS`, `B=[4]`, `m=3,lag=7` はfull-P2 strictだがnontightで近傍が異なる。
- 既知有限域: p1..12とp15で元カードのstrict/full-P2/tight例は0。これは全周期の不存在証明でも
  等式の反例でもない。旧実験の `PASS` はこの件数の正値を要求していなかった。
- 判定: implicationとLean等式の限定意味監査は合格。strict適用領域の非空性と昼の入口検査が未完了。
  `CONJECTURED`、総合**未完了**。

### H-20260920-05: 任意長候補の局所3宣言

- 限定合格対象: `moment_ending_A_budget`、`moment_ending_AA_ss2`、`ss2_intervening_prefix` のみ。
- exact prefix statement: 任意有限語 `w`、`X=w++[A]`。mass X=0、`moment X+|X|<=0`、
  `ssCount X<=2` なら、`X=(u++[S])++v`、`P2(u++[S])`、`v!=[]` となるu,vが存在。
  strict性は `v!=[]`。長さ制限、周期性、OwnerFamily、実軌道なし。
- 非空例: `AASASASASSSA`、prefix `AAS`。負対照: ending-Aを落とす `AAASSS`、mass-zeroを落とす
  `SASASSSA`、moment boundを落とす `SA`、SS boundを落とす `AAASSSSA`。
- 判定: 局所3宣言と紙§1-2の対応だけ限定意味合格。source後半、紙§3-5、各AAS/w1配置、
  true-oldest分解との結合、周期lift、任意長donor回避・削除は未監査。H-05全体の最終定理なし。
  昼の入口検査とwriter補助checker初回prehash欠落により `CONJECTURED`、総合**未完了**。

### H-20260920-04: 非最小lag15延長の反例

- 反証対象: H-02/H-03由来の長さ11 donor回避を、donor最小性なしの長さ15 P2・SS2 donorへ
  置き換える普遍命題。短いB側の条件は保持。
- witness: period16 `SAAASSSASASASAAA`, `u0=15`, `B=[3]`, `lag 3=3`。
  donor `AASASASASSSAAAS` はP2・SS=2、proper P2 prefixは3。B窓は最小AAS、`N(B)=[0]`。
  true oldest offset15・phase0はN(B)に入り、削除後は空なので `1<=0` が偽。
- 強い対照: donor current A、donorはB外、period mass2。有限bound272で得たU `[1,3,11,15]` の
  16 subsets Hallは既存E-181と固定literal計算に依存する補助で、普遍定理ではない。
- 位相境界: 固定offset11はphase4で、真oldest phase0ではない。offset11回避にすり替えない。
- 判定: 9/23独立監査はこの一literalと限定stopを合格。非最小lag15延長のみ `REFUTED`、同一ルート
  `STOPPED`。最小lag15、旧32768/85/46 census、第二w1例、最小p/lag、一般lag、実軌道は未決。

## 必須敵対的検証1-6の適用

1. 入口: 各exact statement・依存差分・非空例・負対照を上に固定。これは再形式化の入口ではなく週間整理。
2. 独立担当: 9/23の各独立監査と原archiveを直接読んだ。今枠の合成案は別Solの合同監査待ち。
3. 空虚性: H-02は非空tight B、H-03は同一長非空例を持つ。H-03 strict/full-P2/tightは未行使と明記。
   H-05は非空例、H-04は非空反例。defined Prop、H->H、自由算術だけへの縮退を既存監査と照合。
4. 意味・反例: donor最小性、full-window P2、true oldest/fixed offset11、periodic signword/actual orbit、
   arbitrary p/arbitrary lagを分離。E-240、E-069、E-345、E-351と照合。
5. 証拠: 今枠は新しい探索・再計算・holdoutを実行していない。9/23 frozen rawを対象hashとともに再利用。
   p32/33、旧censusは新holdoutでも今枠の独立再認証でもない。過去のvacuity/lint/checkは対象source hashが
   一致することを確認しただけで、今枠に再実行したとは記載しない。
6. 記録: 元文、append案、合成full案、逐語監査、command/source hash/manifestを本directoryに保存。
   合同監査が未完了ならlive文書へ適用しない。

## 証拠の来歴

現在のsource hashは9/23監査対象と一致する。H-02/H-03/H-04は
`ShortTightDonorAvoidance.lean` SHA-256 `bb12f35a...fee85`、H-05は
`SS2OldestPattern.lean` SHA-256 `a9540f5f...25de`。HEADは
`08c08565c743f39350c9b959e1df7d30aa1cae5d`。

今枠で行ったのはread-onlyな時計、status、hash、source signature、card、監査・archive照合だけ。
新しい有限計算、seed、cutoff、discovery、holdout、Lean build、vacuity/lint/full checkはない。
過去の対象版では、各9/23監査に保存された独立計算と、vacuity/lint/`./scripts/check.sh` exit0がある。
これらを今枠の再現とは呼ばない。詳細は `commands.md` と `verbatim_signature_audit.md`。

## 失敗・不確実性・次の判断

- H-02: 歴史的entry review欠落と初期失敗run provenance欠落。
- H-03: exact strict/full-P2/tight領域の実現性が未決。有限0件を不存在へ昇格しない。
- H-05: 3宣言以外の後半結合が未監査。全体定理がない。
- H-04: 反例は非最小lag15だけ。最小donorや一般lagへの反証ではない。
- 共通: 全メンバーshort-onlyという制限付きUを完全all-lag供給集合へ、periodic signwordを実軌道へ、
  局所lemmaをsurjectivityへ拡張しない。

次の判断は、この合成案を独立合同監査へ渡し、合格した同一byteだけをlive文書へ適用すること。
新しい独立入力がない限り一般lagルートの継続を推奨しない。再開時は任意p・任意lag・実軌道を分けた
新しいbounded cardを作り、独立入口検査を形式化前に完了する。

## 成果物

- `weekly_report_append_draft.md` / `proposed_weekly_report_full.md`
- `proposed_h0{2,3,4,5}_card_append.md` / `proposed_h0{2,3,4,5}_card_full.md`
- `original_h0{2,3,4,5}_card_at_freeze.md` / `original_weekly_report_at_freeze.md`
- `verbatim_signature_audit.md`, `commands.md`, `SOURCE_SHA256SUMS`, `MANIFEST.md`, `SHA256SUMS`
- `raw/`: 開始時計、status、hash、source/監査の直接抜粋

研究Lean、live card、live週報、handoff、registry、frontier、proof map、root、Audit、gateは変更していない。
stage/commitもない。
