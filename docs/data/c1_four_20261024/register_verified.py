"""Register only the four claims covered by check-second and their statement audits."""
from pathlib import Path
import re,subprocess
prefix='Recaman.BlockSuffixPositivity.'
rows=[
 ['E-390','PROVED-LEAN','actual-S-gap-macro',
  'H-20261024-01。任意padded BlockWord prefix後、先行の全A≤10、非Endable A≤4と正不足の具体条件の下で、任意長S-gap j後の実際のA0/A1はmin(j,19)の有限macroへ移る。長gap後の非供給Aを残し、stepAは第11Aも許す。全長A≤10やr4全分類は仮定・証明していない。12837状態の大規模kernel検証はメモリ上限でSTOPPED、E-388はCOMPUTEDのまま。',
  'Recaman/BlockSuffixPositivity.lean',prefix+'actualFourState_macro',
  '実測で資源を減らせるcheckerまたは数学的な小さいquotientが得られた時だけr4証明書を再開。時間/メモリ上限追加のみでは再開しない'],
 ['E-391','PROVED-LEAN','finite-first-supply-terminal-test',
  'H-20261024-03。任意の実tail wとpadded BlockWord prefix、n≤b、任意future長K。j<2×wの全A個数の全候補でlocal P2も必要old signatureもないという明示Bool terminalSupplyCheck(w)=true、futureの元0基点非Endable A個数0なら、futureの全A個数も0。固定A/語長/深さ上限なし。初期n=bはE-378で処理。finite checkと零追加free予算を仮定に明記し、任意wで成立したとは言わない。',
  'Recaman/BlockSuffixPositivity.lean',prefix+'no_additions_of_terminalSupplyCheck',
  '具体terminal証明書や記号的な無限語族へ適用。checkを結論そのものへ置換しない'],
 ['E-392','PROVED-LEAN','sixteen-root-future-area',
  'H-20261024-04。実zがFourNonsuppliedData.endpointWordsの明示16語のいずれかという条件付き。padded BlockWord prefix、不足0/正不足/終端不足1、future Ay≤1、Fb≤Fnなら任意長/深さfutureのQ:Z≥0。同じ具体条件で全古いt<nのP2を排除。719状態と実語simulation、深さ外はE-379で証明。Int元pのまま接続。16rootの全包含はa_z≤4から未供給で、r4全体や一般C1の証明ではない。',
  'Recaman/BlockSuffixPositivity.lean',';'.join(prefix+x for x in ['sixteen_root_state_member','sixteen_root_area_nonnegative','sixteen_root_no_old_window','sixteen_root_area_int']),
  'a_z≤4から明示16語への分類kernelが残る。具体root仮定を消したと誤記しない'],
 ['E-393','PROVED-LEAN','odd-A-run-terminal-family',
  'H-20261024-05。任意padded BlockWord prefix後、実tail S^m A^r S^jでr奇数かつm≥2r−1なら、元0基点で末端はEndableでない。r/m/jの上限なし。従ってS^m A^r後の追加非Endable A予算0なら任意長futureの全Aも0。local始点は奇数個のAまたは単峰形、old始点はE-385で排除。全r≥3でprefix S A^rとtail S^(2r−2) A^rはmass1/area0かつprefixがBlockWordで、閾値を一様に1下げられない。高不足のterminal族でありC1全体ではない。',
  'Recaman/BlockSuffixPositivity.lean',';'.join(prefix+x for x in ['no_endable_after_manyS_oddA','no_additions_after_manyS_oddA','old_count_barrier_sharp_family']),
  '多runの最後のfree A後を扱う記号的terminal pruningへ。任意rのrankや一般Qは未証明'],
]
p=Path('docs/EVIDENCE_REGISTRY.tsv');text=p.read_text()
assert all(r[0]+'\t' not in text for r in rows)
p.write_text(text+''.join('\t'.join(r)+'\n' for r in rows))
answers={
 'actualFourState_macro':[
 'yes — 同じf/seg/EndNと任意のS-gapを量化し、実際のA0/A1を扱う。',
 'no — hcountは次A直前の全A≤10という明示条件。これをr4全長から供給できたとは主張しない。hbudget/hposは具体count条件でH/Qや結論ではない。',
 'no — 全P2のlocal/old分解、19符号trim、S-gapの飽和とactual-state更新を接続する。単なるstate定義の仮定化ではない。'],
 'no_additions_of_terminalSupplyCheck':[
 'yes — 任意の同じf、実word、BlockWord prefix、元0基点EndN、任意future長Kを量化。',
 'no — hcは有限個の具体Bool検査、hfreeは追加非Endable A数0。全A0という結論や未知のHを仮定せず、claimに両条件を明記している。',
 'no — 最初のfuture Aへの強帰納でS-gapを供給し、E-389で有限範囲へ落として矛盾。n=bはE-378で別に処理する。'],
 'sixteen_root_state_member':[
 'yes — 実fの全prefix/tail/EndNと具体16wordを扱う。',
 'no — hdepthはこの部分定理の明示条件、hwは具体16語のリスト所属。a_z≤4からhwを導いたとは主張しない。最終Qではhdepthを除いている。',
 'no — 全future長の帰納で、実際の全P2のA0/A1を719状態の閉グラフに移す。'],
 'sixteen_root_area_nonnegative':[
 'yes — 同じfのAr/Fw、元0基点のcount、実root16語と任意futureを量化。',
 'no — hwという具体root制限を明記。H/Q/結論を仮定せず、最終statementに深さ/語長上限はない。r4全包含は未供給のまま。',
 'no — 深さ4内は新しい719状態のkernel証明、外は16語の深さから最低訪問をq以後へ供給しE-379へ分ける。'],
 'sixteen_root_no_old_window':[
 'yes — 任意の実old始点t<nとfの全P2窓を扱う。',
 'no — 具体root所属、実不足とAy条件だけ。Winの否定や同値な定義を仮定しない。',
 'no — 仮の実Winからguardを供給し、前半面積≥1と新Q≥0をWinの面積0と矛盾させる。'],
 'sixteen_root_area_int':[
 'yes — Intの元p、e/segment/Endable/countPをそのまま量化。',
 'no — root所属も予算も元pに対応する。途中nへhistoryを切り直さず、具体16語の条件を残す。',
 'yes — 既に証明した自然clockのQを元pへ移すadapter。独立成果として追加計上しない。'],
 'no_endable_after_manyS_oddA':[
 'yes — 同じfの実tail S^m A^r S^j、元0の全EndNとprefixを量化。',
 'no — r奇数/m≥2r−1と実語の形を明示。Endableの否定や未知仮説を仮定しない。r/m/j上限なし。',
 'no — local始点の全分類とarea計算、old始点の全A/S上界を使って全P2を排除する。'],
 'no_additions_after_manyS_oddA':[
 'yes — 任意fの具体run形と元0基点free count、任意future長K。',
 'no — hfreeは追加非Endable A数0で、全A0そのものではない。奇数性/長いS/prefix条件を残す。',
 'no — 最初のfuture Aへの強帰納で実S-gapを供給し、一様なEndable排除を適用する。'],
 'old_count_barrier_sharp_family':[
 'no — binderはNat rだけ。結論は明示された符号語族のBlockWord/mass/area。これはorbitやC1を解決する定理として数えない。',
 'no — r≥3だけで、質量/面積の結論を仮定しない。実現するprefixはSAAAにAを付けた具体語。',
 'no — run面積の帰納式・連結式とBlockWord構成から一様語族を検算する。実fを量化した同じrowの二定理が本体。'],
}
for row in rows:
 rid=row[0]
 template=subprocess.check_output(['python3','scripts/harness_gate.py','--audit-template',rid],text=True)
 template=template.replace('- reviewer: TODO (name, YYYY-MM-DD)','- reviewer: Codex, 2026-10-24 JST（形式化後の別pass。人間レビュー未）')
 def fill(m):
  block=m.group(0);name=re.search(r'^## (\S+)',block).group(1).split('.')[-1]
  for i,answer in enumerate(answers[name],1):
   block=re.sub(r'^'+str(i)+r'\. .*$',str(i)+'. '+answer,block,flags=re.M)
  return block
 template=re.sub(r'(?ms)^## \S+.*?(?=^## |\Z)',fill,template)
 Path('docs/statement_audits',rid+'.md').write_text(template)
# Every newly registered row is linked with its actual limitation.
p=Path('docs/CURRENT_FRONTIER.md');s=p.read_text();point=s.index('\n## 結論')
s=s[:point]+'\n- 本日の検証済み入力: E-390は先行A≤10下の実語macro（全長A上限ではない）。E-391は具体有限checkと零追加free予算から任意長terminal ray。E-392は明示16root条件付きfuture Qで、a_z≤4の全包含は未供給。E-393はr奇数/m≥2r−1の無制限terminal族とsharpness。\n'+s[point:];p.write_text(s)
print('registered E-390..E-393 with exact statement audits')
