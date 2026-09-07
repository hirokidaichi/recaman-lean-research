## 結論・研究質問

任意の有限集合Fを既知履歴に含めても、density・triangular range・canonical parity・blocker一回使用だけでは、blocked-comb survival比 `7hPrev≤16v` は導けない。この紙上countermodel族をLeanで認証する。

**canonical Recamán軌道の反例を作るissueではない。** 実際に証明すべき履歴条件を切り分け、不可能な弱化を再試行しないための形式化である。wrapperや有限サンプルへの弱化を完了として扱わない。

## 正確な対象

任意有限F⊆ℕに対し、正の偶数 `w>max(F∪{0})` と偶数 `D≥10` を `D²-8D>w` となるように選ぶ。

```text
v=D²+w, J=v/2, h=v+1+3J,
n=16h+2·[h odd], b=n-2, c=n+2J+1, x=3n+h-1.

seed = F ∪ {0,x,v-1}
       ∪ {v+3j : 1≤j≤J}
       ∪ {(j-2)c+v+j(j-3)/2 : 4≤j≤D}.
```

clock b、current x、history seedから、strict-positive / fresh subtraction、otherwise additionという標準のstepを実行する。符号語は `SS (AS)^J S A^D S^D`。

証明したいpayload:

- Fと0とcurrentを含む有限seed、`|seed|≤b+1`、`max seed≤b(b+1)/2`、currentのcanonical parity。
- actual stepが上の符号語を生成し、prelanding run J、一歯comb end `(c,v)`、blocked popupを持つ。
- `(c+2D,w)`までresidue increaseがなく、wは次のlate landing。さらに後続wrapが存在する。
- `7h-16v=3v/2+7>0`。
- l3blocked clock c+5の後から着地までのpositive blocked usesはc+6,…,c+Dのみで、全candidateが異なる。

F inclusionは、F以降にseedの残りをcanonicalに共同生成できることを意味しない。

## 紙上依存列と最小の難所

1. 前置SS後のlower railは `c+v+k (0≤k≤J)`、upper railは `2c+v-j (1≤j≤J)`。SSの中間値 `2c+v-(J+1)` を忘れない。
2. `A_j=jc+v+j(j+1)/2`。j≥4のaddition candidateは `A_(j-2)-1` でseedにある。j=1はnonpositive、j=2はv−1、j=3はc+vにより強制。
3. D回のadditionの後、k回減算した値は `A_(D-k)-k²`。**この値の全historyに対するfreshnessが最初の証明単位**。
4. 異なるc係数の帯はc>40vにより非交差。同じ帯のpreloaded値 `A_(D-k)-1` はk≥2の場合にしか存在せず一致しない。
5. level2の下降値の定数項 `w+4D-1` はrunの最小 `v-J-1` より小さい。これが `D²-8D>w`。level1は `w+2D<v`、level0は `maxF<w<v-1`。
6. no-wrap residueの終点は `v-D²=w>0`。seedのtriangular boundは以後も保たれ、no-wrapを続けるなら二歩ごとにresidueが少なくとも1減るため、後続wrapが存在する。

完全な紙上論証: 作業ツリーの `docs/STRATEGY_AUDIT_2026-09-06.md` §3、カードH-20260906-07、E-056。これらの新規ファイルは本issue作成時点では未push。

## 証拠

- `PROVED-LEAN`: 固定seed32値の `(c,v,J,h)=(2213,59,25,135)` から2229で1へ着地する反例と、一回使用の全分類。新モジュール `Recaman/SeededSurvivalCounterexample.lean`。
- `PROVED-PAPER`: 上の任意F族。
- `COMPUTED`: canonical prefix horizon `0,4,128,1000` / 未使用holdout `10000,200000` をFとして、固定seedからPython setで全stepを独立replay、全件PASS。
- 最大例: `w=1345034,D=1164,v=2699930,J=1349965,c=110697147`、次の着地110699475、wrap111420887、seed1497274値、ratio slack−4049902、一回使用1159件。

Base revision: `8a4314d7f65c728d5c6fe6584e1469de4e08332d`。新スクリプト `python3 experiments/survival_countermodel_family.py` で再現。計算は一般証明の代替ではない。

## 受入条件・停止条件

- [ ] 初回90分は、上の3–5のfreshness補題を既存の定義から証明する。紙上主張とLean statementを両方向に監査する。
- [ ] 任意Fの量化子を保持して全payloadを結合する。history membershipやactual generationを仮定で置き換えない。
- [ ] 主要定理を `Recaman/Audit.lean` に登録し `./scripts/check.sh` を通す。
- [ ] H-07 / E-056とproof mapを実際の証拠に合わせて更新する。

紙上freshnessの欠落が見つかったらその不等式と反例を記録して停止する。90分でfreshness補題に届かなければ、残る最小補題を明記し、任意F族全体をPROVED-LEANとはしない。禁止: `sorry`, `admit`, `native_decide`, user-defined axioms。
