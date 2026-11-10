# H-20261111-01 元short三Aと非短record二Aの重複補正

状態 E-644 PROVED-LEAN（`Recaman/ShortRecordOverlapBudget.lean` で Lean 検証済み）。元全run数の実EndN/freeへ接続する限定会計。人間レビュー未。

## 一問

任意f:Nat→Bool、元基点0、任意区間[n,n+K)。LはE637の区間内SAAを持つ元実供給、RはE639の局所非短で元不足の厳密新最低を作る元実供給。Rのうち直前t−1がLの件数をB、直後t+1が同区間内Lの件数をCとする。**3L+2R≤A+B+2C** を元actual countから内部供給できるか。全旧履歴、全run、元EndNを保つ。B/Cは実位置の計数であり、旧源や高Sの一様上限を仮定しない。

## 紙上の最弱edge

各Lは[t−2,t]の3A、各Rは[t−1,t]の供給2Aを占め、各族内は非重複。R位置tは非短。t−1もAなのでL(t+2)はS(t−1)と矛盾。L(t−1)なら重複はt−1のみ、L(t+1)ならt−1/tの両方。L(t−1)とL(t+1)は同時不可。区間境界を含めて、異族の重複をこのB+2Cへ正確に戻せるかが未知。成立してもC1には非record供給と補正項の上界が残る。既存E637の3LとE639の2Rを無条件に加えない。

## 反証・受入・停止

E642の元29..38履歴はR36、EndN35、L37でC型の重複2を持つ。E631では任意途中cutの元free0でも旧源が存在するので、BlockWordを途中でresetしない。E641は全A3族の第一A交互仮定を反証。B/Cをゼロに置かず、E637/639の再証明や未知同値wrapperだけを進捗にしない。最初15分は元位置の補正式、strict候補削減、又は具体反例。続かなければ25分はC型の同高S/同不足と次shortの共同実現、20分は非record Oの低不足帯とE633の接続へ。数学探索worker0、各一修理、個別512MB/10CPU per-process/20wall。

11/10 H53/H54/H69/H39のSTOPを保持。Q36のF9はE636旧<=1まで、長局所のactual接続は未受理。H54は八語一括512MB/4位置版不受理。H39全d absolute actual glueも不受理。資源/tactic/split/import変更だけでは再開しない。r4同表0/0二回その他の過去STOPはPORTFOLIOを参照。一般四run/任意run/rank/C1/Q/H/SL/全射性は未証明。

[11/10 DAILY](RESEARCH_HANDOFF_2026-11-10_DAILY.md)、[任意runの会計](RESEARCH_NOTE_2026-11-10_SHORT_RECORD_CHARGE.md)。

11/10 午後: 不等式は E-644 として Lean 化。形式文は `3*cN (shortEndpoint f n) n K + 2*cN (localRecord f n) n K ≤ additions f n K + cN(rec∧short(t−1)) n K + 2*cN(rec∧t+1<n+K∧short(t+1)) n K`。L/Rは短端点・局所非短recordの区間内count、Bの直前端点は t<n+K-1 から自動内部、Cは直後端点の内部性を明示。E643の紙上のB/C窓と一致することを確認済み。次の未知はB/C自身の上界、非record供給Oの制御、及びこの合計から実際に空きj+4を割り戻す手順。
