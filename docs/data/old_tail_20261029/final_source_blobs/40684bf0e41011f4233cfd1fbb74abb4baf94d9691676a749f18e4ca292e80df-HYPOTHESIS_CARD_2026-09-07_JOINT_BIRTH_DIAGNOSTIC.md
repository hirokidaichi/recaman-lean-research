# Hypothesis card: #71 fixed joint-birth diagnostic

- ID: H-20260907-02
- Status: `STOPPED`（分類はCOMPUTEDとして完了。独立した大域不等式が得られず、正の証明枝を停止）
- Base revision: f05ddcb
- Roles: proposer → falsifier → formalizer → auditor（同一agent、#70完了後に順次実施）
- Started: 2026-09-07 00:15 UTC

## Bounded question

c=11685598221, v=4318940415のcanonical反例一例に固定し、
W={3c+v+5−3i : 0≤i≤31057}の全31,058値のfirst birthを
生成符号・level・arc・生成runの区間に分類する。
これは新しい普遍不等式ではなく、E-057反証後の原因診断である。

## Acceptance and stop

- 一つの共有prefix replayで全Wを追う。first clock、符号、生成segmentの閉形式を保存する。
- scalar stepで得るarc境界とconsumer traceで照合し、W全件を対応付ける。
- 生成runの共有、過去arcからの持越し、producer railの未使用区間を数える。
- 既存telescoping・one-use・density/range/parity・固定prefix inclusionとは異なる定量入力が
  得られた場合だけ、全量化子を持つ新カードと未使用範囲を固定して反証する。
- 60分または一回の分類完了で判定。分類表だけならCOMPUTED、正の証明枝はSTOPPED。

## Falsifier before computation

高速監視の変更は観測器だけに限定し、漸化式・membership・section加速条件を変えない。
7個の既知境界birthを回帰対照とし、加速開始clockの異なる二実行でも全birthが一致するか確認する。
small rangeのplain/accelで同じ観測器を全visited候補に試す。scalar probeのarc境界・最終値・
consumer traceで独立に照合する。計算は一般定理へ昇格しない。

## Dependency and uncertainty

既存paper/Lean E-056は全局所制約と任意Fを同時に課してもsurvivalを壊せる。
従ってfirst-birth分類から新しいarc間の資源不等式へ進むには、生成runが実際の同一軌道で
共存する制約を別に証明する必要がある。単なるラベル付けをその証明と数えない。

## Evidence / acceptance result

2026-09-07: 60分の上限内、最初の分類で判定。Wの31,058値すべてのfirst birthを
高速observerとscalar observerで一致確認。加速開始点2,097,152 / 3,000,000でも一致。
小例はhorizon20,000、targets1..4000、first births3,789件がplain/accelで一致した。
境界7値、scalarのarc表と697,233行のconsumer traceも一致した。
元のscalar probeとのtrace・arc表はbyte単位で同じだった。

- arc40 / q3 / S / 同一lower rail: i=0..25030、25,031件。
- arc39 / q5 / A / 同一upper rail: i=25031..31057、6,027件。
- 二つのrailは隣接。次candidateは結合railより2小さく実際にfresh。
- first birth時刻の共有0、producer runの共有2群。
- 結合rail456,724値のうち425,666値はWに含まれない。他eventで未使用とは主張しない。

## Auditor and stopping decision

分類表とphaseの費用恒等式は`COMPUTED` E-058。初出と再訪、同じarcと前arc、
生産されたrail全体と今回のWで消費した部分を区別した。
`3(v-u)-7J=62-8N`は既存の値・時刻・剰余の恒等式であり、独立したglobal invariantではない。
今回の例は元のsurvival閾値から遠く、その境界で一般評価を検査したものでもない。
新しい不等式の候補0件。係数調整・one-use・fixed-prefix追加の修理へ戻らず、
正の証明枝を`STOPPED` E-059と判定した。一般仮説の新holdoutやLean wrapperは作っていない。
実装の数学的反例・計算不一致は0。残る不確実性はactual producer群の共同生成を
c,v,Jへ拘束するcutoff-independentな評価が存在・証明できるか。

## Handoff

詳細は[共同birth監査](JOINT_BIRTH_AUDIT_2026-09-07.md)。
変更ファイルはカード、監査、3個のobserver/分類スクリプト、exact TSV/JSON/text、証拠台帳。
コマンド・source hashesは[再現記録](data/issues_2026-09-07/README.md)。
#71の有界診断は完了として閉じ、#72で戦略地図を一回更新する。
