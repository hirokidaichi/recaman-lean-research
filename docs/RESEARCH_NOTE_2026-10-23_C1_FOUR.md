# C1 a_z≤4: 全長の計算分類とkernelへの残り

E-388 / COMPUTED。[rankカード](HYPOTHESIS_CARD_2026-10-23_C1_RANK.md)、
[Q4カード](HYPOTHESIS_CARD_2026-10-23_C1_FOUR.md)。**PROVED-LEANなのはE-386/E-387のa_z≤3まで。**

## 完了したprefix-free緩和

任意のpadded BlockWord prefix後、元0基点の正不足prefix、非Endable A≤4を対象にした。
第16Aへ初めて到達する停止線より前では、先行A≤15なのでlocal P2長≤29。
E-385によりold P2にはS≤2A−2が必要で、S≥29ならold supplyはない。
S<29ではtail全体、S≥29では全A/非Endable Aの個数と末尾29符号を保持する。
後者でd≥29−15>1となり、終端d1を失わない。原点をnへrebasingしない。

old supplyは各clockごとに独立な必要mass/area signatureを選べる過大なモデル。
必要条件はE-381のLean上下界・area≥1・mass1ならarea1だけで、E-384の未Leanな存在方向を仮定しない。
実際の全wordはこのモデルに含まれる。各clockのold選択を一つのprefixで同時実現できるとは言わない。

- 全440943訪問、S-saturated状態46892。第16Aなし、観測最大A10。
  停止線までの全グラフが閉じたため、任意長の実入力の全A≤10というCOMPUTEDな上界になる。
- 独立版はforward F/G、literal BlockWord mass≤14の3721語からの498signature、
  逆順DFSとliteral末尾29語で、訪問数・状態数・全endpoint集合・最大A・P最大を全て照合。
- 緩和モデルの終端d1のa_z=4は次の8語。実入力はこの8候補のいずれか（許容old選択が実prefixに同時実現するという主張ではない）：
  SAASAAA / SASAAAA / SASAASAAA / SSAAAAA / SSAAAASAA / SSAAASAAA /
  SSSAAAASAAA / SSSSAAAASAAAA。
  これらは全A≤8・長さ≤13・深さ≤4。a_z≤3はE-386の8語と一致する。
- 修理候補P=A−2(d−1)の最大はr=0..4で0,1,3,7,8。
  任意rのrankや供給A前のslack≥3は証明できていない。

再現: `python3 docs/data/c1_depth_20261023/relaxed_higher.py`、
`python3 docs/data/c1_depth_20261023/higher_independent.py`。
argv/source/revision/dirty hash/CPU上限は同folderのRELAXED_HIGHER_RUN/HIGHER_INDEPENDENT_RUN等に保存。

## Q4

上記16語を開始語とし、Ay≤1、正不足、全tail深さ≤4、Fb≤Fnについて全futureを探索した。
719状態・572guard、Z最小1、最大到達語長22。word長/S数の数学的cutoffなし、保護guard未使用。
別実装が全状態・全edgeをforward areaとliteral old signatureで一致させた。
z深さ4は上のCOMPUTED分類、futureが深さ4を外れる場合はE-379を使う紙上二分により、
a_z≤4の任意長/任意深さのyについてQのCOMPUTED入力が得られる。
**r4分類と719状態のkernel証明書化は未完了。一般a_z≥5も未解決。**

再現: `q4_graph.py` / `q4_independent.py`、Q4_RUNS.json、q4-certificate/q4-independent。

## 停止・反証と次のedge

実prefixによる高予算probeはmass0..4で完了したが、mass5..14のholdoutは
3708context中782完了・1中断・299569152訪問で28秒wall guardに到達。
全体未完了を反例不在の証明にせず、同設定の時間追加をSTOPPEDとした。
prefix-free signatureへ機構を変えた上の完了結果とは区別する。

全prefixのA≤2^r−1は既知語SAAA|SSSSAAAASAでr2/A5/d2となりREFUTED。
終端d1の親命題は未反証。修理Pについてもr≤4の計算を任意rの証明にしない。

次はS-gap上限のE-389を使い、Aが増えるeventだけの証明書とterminal S-rayの閉じ方を評価する。
最高A10のtail S5 A3 S4 A4 S A3は4種の実BlockWord prefixで到達し、future free A予算0なら
以後Aを増やせないこともE-389でLean証明した。これはr4のendpoint分類全体ではない。
次の受入はr4分類の全長kernel証明書、または圧縮で失う条件の具体例。
