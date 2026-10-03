# Hypothesis card: short tight subsets avoid the true oldest donor subtraction

- ID: `H-20260917-01`
- Owner: Astra (計画)、GPT-5.6 Sol / xhigh (研究実行)
- Created: 2026-09-17 JST
- Status: `PROVED-LEAN`
- Research branch: issue #73、G2 の短い緊密集合版。E-359 の先で新しい局所補題が得られるか
- Plan: [1週間の計画](RESEARCH_PLAN_2026-09-17_ONE_WEEK.md)

## Exact statement

以下の全ての `p : Nat`、`e : Int → Bool`、`U B : List Nat`、`lag : Nat → Nat`、`u0 : Nat` について考える。
`past e t d` は新しい順の過去 d 符号、`P2` は `mass = 1 ∧ moment = 0`、`N(B) = neighborhood e p B lag`。
`trueOldestPhase` は E-350 の既存定義を使う。新しい定義は追加しない。

仮定:

1. `0 < p`、`∀ x : Int, e (x + p) = e x`、`0 < signSum e 0 p`。
2. U は重複なく、`u ∈ U` と「`u < p`、`e u = A`、ある `d > 0` に対して `P2 (past e u d)`」が同値。
   各 `u ∈ U` の `lag u` はその最小の正の d。全供給位相を含むことは兄弟の所属を導くために明示する。
3. 全ての `A.Sublist U` について `A.length ≤ (N(A)).length` (Hall)。これは仮定であり証明対象の容量ではない。
4. `u0 ∈ U`、`lag u0 = 11`、`ssCount (past e u0 11) = 2`。従って donor は E-348 の7語のいずれか。
5. `B.Sublist U`、`u0 ∉ B`、`(N(B)).length = B.length`。
6. `∀ b ∈ B, lag b = 3 ∨ lag b = 7 ∨ lag b = 11`。

結論 Q:

```text
trueOldestPhase e p u0 11 ∉ neighborhood e p B lag
```

p に上限を置かない。B が空の場合も含む。donor の lag 11 と SS=2、B の lag 上限は主張の一部。
任意 lag の G1/G2、SS≥3 donor、一般 Gate T6、E-070、E-067、全射性を結論しない。
`|U| < |D|` は本カードの仮定に加えていない。必要と分かった場合は理由と反例を記録し、一回の修理として区別する。

## Why it would matter

- Frontier obligation discharged: E-359 が与える lag 3/7 への縮約を、真の最古 S の回避へ接続する G2 の限定版。
- Stronger than an existing identity: 周期上の実際の符号、被覆、緊密性を使って3配置を排除する必要がある。結論を仮定に入れず、既存 p≤10 の供出則の言い換えにしない。
- Smallest useful consequence: 短い緊密回避 B について供出候補が実際の S であり、その S が N(B) に無いこと。

## Provenance and dependencies

既存の利用対象:

- `PeriodicOwnerFamilyLagEleven.tight_lag_three_or_seven` (E-359)。B の lag 11 を排除する。
- `LagSevenDonorCoverage.lag7_cover_classification` / `minimal_ss2_eleven_mem_donors` (E-348)。lag 7 の被覆は w1 の newest S、donor d1/d2/d4 に限る。
- `TrueOldestGateT6.aas_endpoint_ne_trueOldest` / `trueOldest_is_subtraction` (E-350)。lag 3 の場合と no-op の排除。
- `TightHallAugmentation.hall_forces_membership` / `w1_sibling_forced` (E-351)、`TightPrivatePhase.private_phases_le_one` (E-355)。必要な所属・相異性・modulo の条件を元の signature から供給する。
- `HallMatching.tight_owner_map` (E-358)、`OwnerFamilyLagEleven` (E-357)。所有者モデルを使う場合は周期上の構成を省略しない。

非形式的な依存鎖:

```text
全供給 U と最小 lag + Hall + 緊密 B + B の短い窓
  -> E-359 で B の窓は lag 3/7
  -> lag 3 の端点は E-350 で donor の最古 S と不一致
  -> lag 7 の被覆は E-348 の3配置のみ
  -> [未知] その3配置と緊密性・所有者の整合性が矛盾
  -> Q
```

最初に試す最弱の局所入力 W は、上記の周期・全供給 U・最小 lag・Hall の下で、
緊密 B の全メンバーの lag が3/7なら、全ての `t : Int` について次が成立するという含意:

```text
phase p t ∈ B ∧ lag (phase p t) = 7 ∧ past e t 7 = w1
  -> e (t + 1) = true
```

W には donor、回避、Q を仮定しない。donor 側には、E-348 の被覆3配置で donor の bit から
`e (t + 1) = false` を導く小補題を分離する。この二つの符号の不一致で Q を狙う。
`t+2` も加算位相になることや B に入ることまでは W の結論に含めない。
E-351 の `aas_after_w1_forced` は既に `e (t + 1) = A` と未来位相の U 所属・lag 3 を要求するため、
W の証明に逆用しない。周期境界は `phase p t` で処理し、Nat の加算だけで位相範囲を越えない。
W 自体は未証明であり、OS/MD を先取りする可能性があるため、成立条件と反例を先に調べる。
単に `OwnerFamily` の場を増やして必要条件を仮定することは合格にしない。

## Falsification plan

- Small and boundary cases: 7 donor 全て、B=空/単元/2要素、p=1..11、p=12..22、u0=0 と周期境界を跨ぐ配置。
  p が窓長より短い場合の同じ位相の再出現を明示的に扱う。
- Negative controls: E-240 の period 18 の非AAS緊密集合は許す。d1/d2/d3/d6 の offset 11 を最古 S と誤認する実装は失敗させる。
  SS≥3 の最古 S 回避の反例 (E-345)、一般最古 S 単射の反例 (E-069) を、今回の前提から除外される理由ごと記録する。
- Weakened model: 周期性、U の完全性、Hall、最小性、B の lag 制限を一つずつ外して調べる。
  弱化モデルの反例を Q の反例と混同しない。line model の有限配置が無限家族に延長できると推測しない。
- Discovery / regression: 既存 p≤22 の census、E-348 の3配置、既存 lag≤15 の配置。既知の p≤31 の結果も discovery 扱い。
- Frozen holdout: Q と checker を固定した後、p=32,33 それぞれ正符号和の相異なる符号語2000件を固定 seed `2026091801` から生成する。
  生成方式・bit 順序・採用条件をコードに明記し、初回実行前にソースの hash を記録する。各語の全供給 A の最小 lag は p(p+1) まで調べる。
  Hall が成立する語で lag 11・SS=2 donor を取り、lag 3/7/11 のメンバーだけからなる全ての緊密回避 B について Q を検査する。
  U は短い窓だけに切り詰めず、Hall 検査には全供給 U を使う。実際に対象 donor が現れた語が各 p で20件未満なら証拠不足とする。
  実行時間の上限は一晩30分。完走できなければ到達件数・中断条件を記録し、凍結 holdout は未完了とする。
  結果を見て範囲を縮めて合格にしない。Hall は既存 matching 実装と独立な小例の全列挙を照合し、大きい周期で全部分集合を無条件に列挙しない。
  この holdout は現在未実行。実行前に同じデータ・命題の既使用が判明したら、新範囲を宣言して凍結し直す。
- Maximum one permitted repair: 反例のどの前提が欠けるかを説明して一回だけ修理。反例除外専用の例外列挙、p 上限の導入によるすり替えはしない。
- Stop: 元の Q に反例が出れば `REFUTED` として保存。修理版も破れた場合、または計2晩の証明探索で循環しない依存鎖が得られない場合、ルートを `STOPPED` にする。
  計算打切りは不明。未証明 Q 自体は `CONJECTURED` のまま残す。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-17 | `CONJECTURED` | `08c08565c743f39350c9b959e1df7d30aa1cae5d` の E-348/350/351/355/357/358/359 の文書・signature を確認 | 計画時に Q を凍結。新しい反証 probe、holdout、紙上証明、Lean 実装は未実施 |
| 2026-09-17 | `CONJECTURED` | Sol による読取専用の事前レビュー | 最弱の候補を W: w1 メンバーの次符号 A の強制、と明示。E-351 への逆向き依存を禁止。U の完全性と最小 lag は必須の作業前提として保持 |
| 2026-09-20 | `OBSERVED` | 同じ HEAD、`python3 -u experiments/issue73_20260920/baseline_q_w.py 11`、[V2 manifest](data/issue73_20260920/SHA256SUMS)、[独立監査](adversarial_audits/H-20260917-01_20260920_0100.md) | p=1..11 の正符号和語1,872件、Q 非空52件、W 適用32件、違反0。p8/p10 の非空例・E-240・偽 offset 11 を独立再現。一般 Q/W は未証明、Lean 入口は差戻し。初回 p=1..15 は未完了で、回復実験により成功扱いにはしない |
| 2026-09-20 01:30 | `OBSERVED` | 同じ HEAD、[候補版 manifest](data/issue73_20260920/slot0130/SHA256SUMS)、[独立監査](adversarial_audits/H-20260917-01_20260920_0130.md) | 既知有限回帰は再現。新規反証ゲートは重複period行と負値相殺payloadを受理し、手続判定は差戻し。修理枠使用済みのため当該ゲート実装枝を停止し、採用しない。Q/Wの反例ではなく、命題・量化子・証拠水準の昇格はない |
| 2026-09-20 02:00 | `CONJECTURED` | 同じ HEAD、[実行版 manifest](data/issue73_20260920/slot0200/SHA256SUMS)、[独立監査](adversarial_audits/H-20260917-01_20260920_0200.md) | 元Q/Wの状態を維持。U完全性だけを外したproper-Uモデルはp1..11のw1前件0件で手続判定は未完了。exit0やEXHAUSTED_ZEROを成果とせず、初回誤計数・v1ソース未保存・修正版の非空受入不足を記録。第2修理・範囲拡大・Leanなし |

## Semantic audit

- Informal -> formal: e/p、U の完全性、最小 lag、Hall、donor 7語、回避・緊密、B の lag 上限を signature と照合する。
- Formal -> intended consequence: 結論は真の最古 S の非被覆そのものとし、周期の隠れた上限と追加の未証明 Prop がないことを確認する。
- Counterfactuals: SS≥3、lag 上限なし、自由配置、U 不完全の各モデルを別々に検査する。
- Vacuity: donor と非空 B が同時に存在する例を示す。削除対象が A になっていないか、仮定の不整合だけで証明していないかを調べる。
- Scope: 対象は周期符号語。実 Recamán 軌道の生成可能性や全射性の証明としない。
- Downstream: Q から donor を含む全ての部分集合の削除後 Hall 保存は出ない。既存の接続には p≤11 が残る。

## Decision

- Mandatory adversarial gate: [週間計画の必須条件](RESEARCH_PLAN_2026-09-17_ONE_WEEK.md#必須の敵対的検証)を Q、W、反例、計算結果の全てに適用する。実装者とは別の Sol が元の定義・signature・証拠を攻撃し、対象版を明記した監査記録が合格するまで成果登録・昇格しない。
- Card-specific attacks: U の完全性・最小 lag・Hall が結論の言い換えにすり替わっていないか、E-351 による W の循環証明、偽の offset 11、位相の同一視、空の検査対象を必ず調べる。Q の donor と非空 B の実例、W の w1 メンバーの実例はそれぞれ別に確認し、Q と W の全前提の同時充足を要求して結論の矛盾を前提にしない。
- Audit status: 01:00のV2有限回帰は限定合格。01:30のゲート実装は差戻し・停止。02:00は完全性だけを外す弱化検査の入口を独立監査したが、実行結果は前件0で未完了。[最新監査](adversarial_audits/H-20260917-01_20260920_0200.md)に対象版・原出力・欠落を記録した。一般Q/W、全弱化モデル項目、一般の位相移送は未完了、Lean入口は差戻し。検査器の欠陥や対象0をQ/Wの反証・支持にしない。
- 次: [当日の引き継ぎ](RESEARCH_HANDOFF_2026-09-20_SOL.md)に従い02:30は監査・記録を優先。第2修理や範囲拡大で対象0を回避しない。再開にはproper U上の非空tight w1例、または独立な別の一問と事前固定した受入条件への監査が必要。既使用の診断値を事後に有限分類の成功や新holdoutへ変更しない。
- 現在: 命題 `CONJECTURED`、既知有限結果のみ `OBSERVED`。今回の弱化モデルは未判定、手続き上は未完了。ゲート実装枝と本枠の実験は停止したが数学ルート全体の停止ではない。holdout・紙上証明・Leanは未実施。新しい証拠台帳行・Lean定理は登録しない。
- 9/20夜の終了確認: [02:30独立監査](adversarial_audits/H-20260917-01_20260920_0230.md)は記録整合性と本夜閉鎖判断だけ合格。停止範囲の文言を既存の具体枝へ限定し、原版を保存した。数学的な状態・量化子は不変。次回は当日引継ぎの再開条件に従い、未完了や差戻しを確立前提へ流さない。
- Reopen only if: 停止した場合は、未知の3配置排除を支える独立な局所補題、または停止理由を分離する正確な追加条件が得られたときだけ。

## 2026-09-21 01:00: 昼の候補を取り込む前の独立監査

Status は `CONJECTURED` のまま。上の9/20夜終了時点の「holdout・Lean未実施」は歴史的記録であり、
現在の状態ではない。9/20昼の別セッションにより局所 W / Q の Lean 候補が追加され、
元の p32/33 各2000語、seed `2026091801` の holdout も実行済みとなった。
既使用データを新 holdout と呼ばず、昼の同作者別アルゴリズム比較を独立担当の検証と呼ばない。

[01:00独立監査](adversarial_audits/H-20260920-01_20260921_0100.md)では、
ShortTight source SHA-256 `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85` の
`short_tight_avoids_ss2_donor` までと必要な構成に限り、独立 Sol が数学・意味を合格と判定した。
E-351循環、隠された結論、真のoldestと固定offset11の混同は検出されず、非空例・弱化対照を再計算した。
局所 W の OwnerFamily 仮定は周期版で構成され、最後の短い Q の Hall は短い窓の内部で証明されるとの監査結果。
元の量化子・結論を本追記で変更してはいない。

ただし **総合手続判定は差戻し**。全体 `./scripts/check.sh` は未監査の
`Recaman.SS2OldestPattern` が root closure 外のため exit 1、正式な G5 statement audit も未完成。
昼の形式化前独立入口検査は当時未実施であり、今回の事後監査を事前検査として扱わない。
独立 checker の初回修正前 source / raw 未保存という証拠欠落も監査記録に明記した。
単体 build と依存込み110 jobsの成功だけで昇格せず、新台帳行・証明マップ更新はない。

p32/33 holdout の全体認証、`short_supply_donor_deletion` 以降の拡張、長さ15反例、
`SS2OldestPattern` は未完了・今回の対象外。限定 Q から一般 Gate T6 や実軌道へ進めない。
元カードの監査入力版は [凍結コピー](data/issue73_20260921/slot0100/original_card_at_freeze.md)に保持した。
次回は [9/21引継ぎ](RESEARCH_HANDOFF_2026-09-21_SOL.md)から差戻し事項を確認し、
対象・依存が変わる場合は再監査する。9/20の停止済みゲートや前件0件probeは再開しない。

## 2026-09-21 01:30: 正規検査の回復と登録前資料

[01:30独立監査](adversarial_audits/H-20260920-01_20260921_0130.md)は、今回の限定修復を **合格**、
正式な新規登録・昇格を **未完了** と判定した。Status は `CONJECTURED` のまま。
rootへ既存SS2OldestPatternの通常importを1行追加し、ゲートを変えず全体checkを回復。
独立実行を含め `./scripts/check.sh` exit 0、392 jobs、公理監査2572となった。
数学3sourceのhashは01:00と不変。import追加をSS2OldestPatternの意味認証にしない。

core10定理と構成2件の全binder・逐語82行・定義展開・双方向意味・非空/負対照を
[登録前packet](data/issue73_20260921/slot0130/statement_audit_pre_registration.md)にまとめ、別Solが再照合した。
既存E-359の説明が証明抽出前のままという不一致も修正し、構成helperと呼出側wrapper、
既存proofの抽出と新規性を区別した。signature・台帳行・数学的主張は不変。
今回checkerの誤ったp8 B指定による失敗は、旧source/rawごと保存した。

正式な新規E番号、登録対象symbol list、正式G5文書と当該行の機械検査は次の判断に残す。
前枠と昼の履歴欠落を遡及解消せず、後半定理・使用済holdout・一般Gate T6へ合格を広げない。
登録前packetのSHA-256は `7b0c3da12f240e5d2a5b4f56bfe11ed08f435bf3cc3cb6a7af3d4e8372149af9`。
本追記前のカードは [01:30入力版](data/issue73_20260921/slot0130/original_card_at_entry.md)として保存済み。

## 2026-09-21: E-360 registration

`PROVED-LEAN` E-360 registers
`Recaman.ShortTightDonorAvoidance.short_tight_avoids_ss2_donor` at frozen source SHA-256
`bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`.
For every positive-period sign word, if a nodup tight B consists of in-range current-A phases whose
windows are minimal P2 with lag in `{3,7,11}`, and the donor is a minimal lag-11 P2 window with
SS count 2, its true oldest S phase is outside `neighborhood e p B lag`. There is no period upper
bound. Ambient U, an assumed Hall condition, and positive drift are absent because the theorem
proves Hall for every short sublist from the existing short selector.

This proves the original card's Q. `U.Nodup` plus `B.Sublist U` gives `B.Nodup`; U completeness
gives phase bounds, current-A and P2 windows for B; the old minimal-lag condition gives B's
minimality hypothesis; and `u0 ∈ U` with `lag u0 = 11` gives donor P2 and minimality. The old
positive drift, remaining ambient-U completeness, assumed Hall, and `u0 ∉ B` are unused in the
E-360 application. Thus the exact original Q follows from E-360 without changing the original
quantifiers. General Gate T6, arbitrary lag, actual Recamán orbits, E-070/E-067, and surjectivity of the
Recamán sequence remain unproved. The used p32/33 holdout remains finite evidence, not the proof.

The registration was independently checked against the three frozen source hashes, all 10 core
theorems and two existing constructors, nonempty and weakened-model controls, and official G5.
The missing daytime entry audit and the 01:00 checker-source retention gap remain historical
process debt; the later audit does not rewrite that history.

## 2026-09-24 01:00: 週間監査の限定追記

対象版の独立監査記録:
[`H-20260917-01_20260924_0100`](adversarial_audits/H-20260917-01_20260924_0100.md)。
手続上の適用条件は、親が同記録の最終判定、対象hash、原ログ、および本案とのbyte一致を確認すること。

週間報告で確立済みとして述べられる範囲を、E-360の登録・公式G5・原source・9/21の独立監査と再照合した。
`short_tight_avoids_ss2_donor` は任意の正周期 `p` を扱い、p上限はない。一方、緊密Bの全窓は
最小P2のlag 3/7/11、donorは最小P2 lag11かつSS=2に限定される。ambient U、仮定Hall、positive drift、
donorのU所属、実軌道はQのsignatureにない。短窓Hallを内部で証明するためであり、一般lagや一般Gate T6を
得たことにはならない。

Wの二結論 `own t = t - 7` と `e (t+1) = true` は、4フィールド
`window/addA/own_mem/onto` の `OwnerFamily` を明記して仮定する条件付き局所定理である。
現登録証明では周期的Bへの適用にE-358/E-359の具体的構成を使う。この現適用経路を省いてWを
無条件化しないが、その構成が数学的に唯一とは主張しない。E-351の `aas_after_w1_forced` は
`e(u+1)=true`、未来位相 `w=u+2`、`w in U`、`lag w=3` 等を既に仮定するため、Wのnext-A証明へ
逆用していない。既存の `ownerFamily_of_minimal` と
`tight_owner_family` は依存の抽出であり、E-360の新規成果には数えない。

使用済みp32/33標本は有限証拠で、全体の独立認証は未完了のまま。昼の形式化前独立入口検査欠落と
01:00 checker初回source/raw欠落も後続監査で遡及解消したことにしない。E-240の非AAS緊密集合、
E-069/E-133の最古S単射反例、E-345のSS>=3削除対照、固定offset11の誤りは、Qの正確な局所範囲と
両立する負対照として保持する。

結論: H-20260917-01は登録済みE-360の正確なQ/Wについて `PROVED-LEAN` を維持する。
未解決はlag 15以上を含むB、任意lag donor回避・削除、完全all-lag U、一般Gate T6、実軌道、
E-070/E-067、全射性。この週間計画では範囲を延長しない。
