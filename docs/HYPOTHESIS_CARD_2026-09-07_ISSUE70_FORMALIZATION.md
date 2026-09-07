# Hypothesis card: #70 任意finite-prefix反例族の形式化

- ID: H-20260907-01
- Status: `PROVED-LEAN`（一般族の全payloadをAudit登録・full check済み）
- Source revision: 8a4314d7f65c728d5c6fe6584e1469de4e08332d + 2026-09-06 working-tree artifacts
- Role order: proposer → falsifier → formalizer → auditor（同一agentが順に実施）

## Exact question / acceptance

issue #70とH-20260906-07の全量化子・seed・符号語を保持したまま、任意の有限Fを含む
survival反例族をLeanで証明する。最初の作業単位は、下降値 `A_(D-k)-k²` がF、初期seed、
前置run、全addition出力、先行subtraction出力の全てに対してfreshであること。

パラメータは正の偶数w、偶数D≥10、D²−8D>w、Fの全要素<w。
`v=D²+w`, `J=v/2`, `h=v+1+3J`, `n=16h+2[h odd]`, `b=n−2`, `c=n+2J+1`。
seedとwordは前カードのまま。List表示では重複を許し、scaleにF.lengthも含める。有限集合はその列挙Listを取ればよい。

受入条件: arbitrary F / actual Basic.step / seed bounds / parity / maximal prelanding run /
blocked one-tooth comb / first subsequent late landing before wrap / ratio violation / one-use。
主要定理をAuditに登録し `./scripts/check.sh` を通す。単なる有限例や抽象interfaceへ弱化しない。

## Falsification before Lean

前回の固定discovery/holdoutはそのまま保存する。今回は形式化時の境界監査として、空F・非canonicalなF・
最小w=2,D=10・Dを大きくした場合をexact replayする。負の対照は `D²−8D=w` とし、
省略しやすいSS中間値への衝突が実際に起きるかを見る。これは新しい一般仮説のholdoutではない。

## Dependency chain

1. 帯ごとの値の閉形式と非交差。最小の新規補題は全historyへのfreshness。
2. seed membershipによる強制A、freshnessによるSをstep帰納へ接続。
3. 実値・剰余・seed bound・parity・一回使用を結合。
4. 任意有限Fに許容w,Dが存在することを供給して一般反例族にする。
5. 論証と形式文を両方向に監査し、Audit/full build後のみPROVED-LEANへ更新。

## Stop

紙上freshnessに反例があればその箇所を記録して停止。初回90分でfreshnessに届かなければ、
最小残余を示してその作業単位を判定する。未完成の一般族を完成としてissueを閉じない。

## Evidence log

2026-09-07: 着手。過去の計算結果と紙上証明を読み、既存countermodel / replayモジュールを検索済み。

2026-09-07: 完了。`finite_prefix_survival_countermodel : ∀ F : List Nat, ∃ g, ...` を証明。
全historyへのfreshness、actual word、全隣接residue比較、最初の後続late landing、後続wrap、
seedのサイズと値域・parity、popup/l3 blockage、positive useの完全分類・単射性を含む。
証明は8モジュールに分け、11主要宣言を追加監査した。`./scripts/check.sh` は全体PASS、
264 library modules、監査1,217宣言、許可された公理依存のみ。

## Auditor: both directions

- 任意のFに対しM=max(Fの全要素,F.length)、w=2(M+1)、D=2(M+10)を明示的に選ぶ。
  存在量化の証明に十分なcofinal部分族であり、固定サンプルへの置換ではない。
- Geometryのsize_eqは2J=D²+w、B+2の式は元のn=16h+2[h odd]。
  X=3c−J−3は3n+h−1。seedのA_p−1は元のp+2添字の式と同じ。
- Lower/upper railの全値と開始前のlevel3→2が最大prelanding runを固定する。
  combのv−1とpopup testの既訪問により、一歯で終了する。値の列は実stepから証明済み。
- first_late_landingは途中の全stateがclock以上であることを含む。
  no_wrapは全隣接比較であり、端点だけの比較ではない。後続wrapの存在も別途証明した。
- candidate_seen_iffは5<l≤2Dを覆い、着地stepも含めてpositive blocked usesを分類する。
- Listの長さをb+1以下に抑えているので、集合としてのseed cardinalityにも同じ上界がある。
- Fを含むことと、F以降にseed全体をcanonicalに生成することは区別する。
  canonical survival、全射性、非全射性は証明していない。

## Failed attempts and decision

数学的なfreshness反例は見つからなかった。弱化した境界D²−8D=wでは、SS中間値9937に衝突し、
clock4957で期待Sが実Aになる。strict clearanceは省略できない。
途中のLeanエラーはNat/Int cast、添字書換え、利用できないtacticの修正で解消し、
formal statementの弱化による回避はしていない。
再現: `python3 experiments/survival_family_boundary_audit.py` と `./scripts/check.sh`。
source hashes・境界のexact output・check summaryは`docs/data/issues_2026-09-07/`。
#70を完了と判定し、次は#71の固定したblocker共同生成分類へ進む。
