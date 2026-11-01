# 戦略監査 — 2026-09-06

## 結論

非全射性の主目標に置かれていた自由なcutoffのlanding floorは、実は無条件の帰結だった。
必要なのは、未訪問を確認したprefixと**同じcutoffから先**を排除する入力である。
また、blocked-comb survival比をlocal recurrence、history density、parity、blocker一回使用から
導くことはできない。任意の固定finite prefixを含めても破れるexact seeded反例族を得た。

これは全射性・非全射性の決着ではない。成果は、誤った十分条件の修正と、次に証明すべき
history入力の切り分けである。次の優先順位は[戦略地図](STRATEGY_MAP_2026-09-06.md)を参照。

Source revision: `8a4314d7f65c728d5c6fe6584e1469de4e08332d`。
各実験のsource hashとexact outputは[`data/strategy_2026-09-06/`](data/strategy_2026-09-06/)に保存する。

## 1. 自由なcutoffは新しい数学的入力ではない

`EventualEscape.lean` の主張は次である（`E-052`, `PROVED-LEAN`）。

```text
∀ B, ∃ N, ∀ n≥N, B<a(n).
```

証明は初等的で、missing targetも全射性も仮定しない。

1. `s<t`, `a(s)=a(t)=v`なら、clock tで減算することはfreshnessに反する。
   加算で出現するなら `a(t)=a(t-1)+t≥t`。従って `t≤v`。
2. vが一度も現れなければ常に避ける。出現時刻sがあれば `max(s,v)+1` 以降で避ける。
3. 有限集合 `0..B` のavoidance cutoffの最大を取る。

したがって、任意のpredicateで選んだ時刻（arc bottomも含む）のeventual floorも無条件。
この証明はcutoffの数値上界を与えず、出現時刻を選ぶことに依存する。
既存の `a_succ_ne_of_seen` と同じ機構を全値へ合成したもので、未知の漸近成長率を得たとは扱わない。

意味監査のcanonical証人は4である（`E-053`, `PROVED-LEAN`）。

```text
4 ∉ valuesThrough(4),
∃ N, ∀ n≥N, 4<a(n),
a(131)=4.
```

よって「未訪問prefix H」と「独立に選んだeventual cutoff N」は合成できない。
正しい十分条件は

```text
m ∉ valuesThrough(H)  ∧  (∀ n>H, m<a(n))  ⇒  ∀ n, a(n)≠m.
```

この接続は `missing_of_prefix_and_same_cutoff_floor` で認証したが、研究invariantとして数えない。
arc-bottom版を使う場合には、Hを跨ぐarcと将来の全着地がfloorの対象に入ることも証明する必要がある。

また、`b(n)=n`, `f(n)=floor(n/2)` は全射でrising floorを持つ。従って `f→∞` だけから
欠損値の存在・無限性は出ない。単調な有効floorの下に**実際に未訪問値がある**ことが別に必要である。
この一般sequence反例もLean化した。Recamánの全射性を反証・証明した例ではない。

旧 `H-20260902-05` / `E-028` の自由cutoff routeは `STOPPED`。
852655を同じ検証済みcutoffから先に排除する強い命題は未解決のままである。
[Chaffinの計算](https://benchaffin.com/recaman/recaman.html)は10^612項を超える有限計算と
その範囲での852655の欠損を報告している。そこから未知の無限tailへ量化子を移すことはできない。

## 2. local survival比のexact反例

`SeededSurvivalCounterexample.lean` は次の有限seedから全stepをkernelで実行する（`E-054`）。

| 量 | 値 |
|---|---:|
| seed boundary / current | 2160 / 6620 |
| seed個数 / 最大値 | 32 / 8919 |
| prelanding run start n / 高さh / pair数J | 2162 / 135 / 25 |
| comb末端 c / v / T | 2213 / 59 / 1 |
| 次のlate landing | `(2229,1)` |
| 最初の後続wrap | 2232 |
| survival比 | `16·59=944 < 945=7·135` |

seedは `0,current∈seen`, `|seen|≤b+1`, `max seen≤b(b+1)/2` とcanonical current parityを満たす。
時計2160から2231まで剰余は増加せず、2232で増加するため、二つのlandingは同じcompleted arc内にある。
level-3 candidateがclock2218で塞がれ、level7まで上昇して七連続減算で1へ戻る。

`s=2218`, `e=2229`の間のpositive blocked usesは

```text
clock 2220: candidate 6700
clock 2221: candidate 8919
clock 2222: candidate 11139
```

の三件だけで、再利用はない。このexact分類もLeanで認証した。
従って `E-051` の多重度2が真でも、それとseed boundsだけではsurvival比は導けない。

ただしこの最初のseedは1を欠く。canonicalはclock1で1を訪問しているため、**これだけを
full canonical provenanceが必要な証拠とするのは弱い**。この弱点を次の二段で監査した。

## 3. 固定prefixの追加でも壊れない反例族

まず `F=valuesThrough(128)`（116値、最大495）を含める凍結stress testで、
`(c,v,J,h)=(2883,76,33,176)` から同じarcの `(2901,5)` へ至るexact反例を得た。
比は `1216<1232`、seedは143値。これは `COMPUTED` であり、一般族とは分ける。
5はこのFには含まれないが、canonicalではclock129で出現するため、この例も標準軌道とは言わない。

さらに特定の小値を欠くことに依存しない、次の族を得た（`H-20260906-07`, `E-056`, `PROVED-PAPER`）。

任意有限集合Fに対し、正の偶数 `w>max(F∪{0})` と偶数 `D≥10` を
`D²-8D>w` となるように選ぶ。例えば十分大きい偶数Dを取ればよい。

```text
v=D²+w,  J=v/2,  h=v+1+3J,
n=16h+2·[h odd],  b=n-2,  c=n+2J+1,  x=3n+h-1.

seed = F ∪ {0,x,v-1}
       ∪ {v+3j : 1≤j≤J}
       ∪ {(j-2)c+v+j(j-3)/2 : 4≤j≤D}.
```

このseedからexact word

```text
SS (AS)^J S A^D S^D
```

を生成でき、`a(c)=v`, `a(c+2D)=w` になる。以下は全パラメータの紙上検査である。

### 前置runのactual generation

最初のSSは `x→2n+h→n+h`。その後のAS runのlower railは
`c+v+k (0≤k≤J)`、upper railは `2c+v-j (1≤j≤J)`。
最初のSSの中間値は追加の `2c+v-(J+1)` である。この一値を省略してはならない。
ASのaddition candidateは `v+3j` でseedにあり、lower railはfresh。
最後のSはfreshなvへ着地し、v−1はseedにあるので一歯comb endになる。
q=3→2→1で入るためrunの開始は前置segment内で確定している。

### popupと連続減算のfreshness

`A_j = jc+v+j(j+1)/2` と置く（`A_0=v`）。最初のAはnonpositive candidate、
二歩目はseedのv−1、三歩目はrun最後のc+vにより強制される。
j≥4のaddition candidateは `A_(j-2)-1` で、明示seedに含まれる。

D回のaddition後、k回のsubtractionの出力は

```text
A_(D-k) - k²,   1≤k≤D.
```

である。全ての定数項は `[-2v,3v]` 内にあり、異なるc係数の帯は `c>16h≥40v` により交わらない。
同じ帯の履歴との比較だけが残る。

- earlier addition出力 `A_(D-k)` とはk²だけ異なる。
- 同じ帯のpreloaded candidateは `A_(D-k)-1`。それがseedに存在するのはk≥2の場合だけなので一致しない。
- level3のinitial currentの定数項は `v-3J-3<0`。subtraction出力の定数項は `w+6D-3>0`。
- level2ではsubtraction出力の定数項が `w+4D-1`、prelanding railの最小定数項が `v-J-1`。
  前者が後者より小さい条件は正確に `D²-8D>w`。
- level1のsubtraction出力の定数項 `w+2D` はvより小さく、lower railの下にある。
- level0の終点wはFの最大より大きく、v−1と他のsmall seedより小さい。

従ってすべてのSが正でfreshであり、最後の値はwである。

### no-wrap、seed bounds、one-use

addition j歩目の剰余は `v-j(j-1)/2`。その後k回のsubtractionの剰余は
`v-D(D-1)/2-kD+k(k-1)/2`。最終剰余が `v-D²=w>0` なので途中にwrapはない。
前置runの剰余も `h+5→h+2→h→…→v` と減る。
exact tailも `a(t)≤t(t+1)/2` を保つ。no-wrapならlevelの分だけ剰余が減り、level0の次は
level1なので二歩で少なくとも1減る。従ってこのarcは有限で、二つのlandingを含むcompleted arcがある。

`|F|≤w`, `D≤v`, `J=v/2` よりseed個数は `h+2≤b+1`。
最大値は `max(4n,2nv+2v)≤n²/4≤b(b+1)/2`（本構成ではn≥16h、h≥256）。
nのmod4をhの偶奇に合わせたためxのparityもcanonical clock parityと一致する。

`h=5v/2+1` なので `7h-16v=3v/2+7>0`。survival比は一様に破れる。
最初のl3blockedはc+5。その後、e=c+2Dまでのblocked usesはc+6,…,c+DのD−5個だけで、
異なる帯のcandidateなので多重度は1である。

この族は任意の固定finite prefix inclusionにも耐える。ただしseed全要素のjoint birthを
そのprefixから生成してはいない。この区別が次の研究gateである。

独立set replayはprefix horizons `0,4,128,1000` をdiscovery、`10000,200000` をholdoutとして全てPASS。
最大例はprefix最大値1,345,032より上のw=1,345,034へ着地し、seed 1,497,274値、
ratio slack −4,049,902、多重度1だった。一般族の証明は上の論証であり、この有限検査の外挿ではない。

## 4. preloadなしの対照群

単一初期値zを与えてclock0から実生成した20,001軌道について、各2M clockで
一歯blocked・continued survival比を検査した（`H-20260906-05`, `E-055`, `COMPUTED`）。

| 凍結群 | 完走orbit | 適用record | completed arc | 違反 |
|---|---:|---:|---:|---:|
| discovery z=0..1000 | 1,001 | 102,615 | 30,921 | 0 |
| holdout z=1001..20000 | 19,000 | 2,574,833 | 1,414,202 | 0 |

z=0の59適用recordは既存probeと `(c,v,J,h,nextLandingClock)` 単位で完全一致した。
他のzはcanonicalではない。finite cohortは全z・全clockの証明にならず、
「初期値0に固有」か「追加preloadなしで共同生成することが本質」かは未決である。

## 5. 重み付き着地下降の候補はholdoutで反証

次の新しい候補を、discoveryを見る前に固定した（`H-20260906-08`）。
canonical completed arcのT=1、hasRun、blocked comb end `(c,v)` と、
同じarcで最初の後続late landing `(e,u)` に対して

```text
7J ≤ 3(v-u).
```

これが真なら `u≥1` によりsurvival比が従う。既存lockの一対あたりの費用7が動機だったが、
phaseを跨ぐと維持されるかは未知であり、定理としては使わなかった。

canonicalを0から200億clockまで生成し、全56,580 comb recordを監査した。

| 凍結群 | 適用record | break / l3blocked | 違反 |
|---|---:|---:|---:|
| discovery c<10^9 | 1,221 | 959 / 262 | 0 |
| holdout 10^9≤c<2·10^10 | 3,228 | 2,500 / 728 | 5 |

最初の反例は `(c,v,J)=(11685598221,4318940415,276986)`、
次の着地は `(e,u)=(11685741477,4318376915)`。
`3(v-u)-7J=1681500-1939902=-248402` で、5件すべてl3blocked、同じarc40内だった。
独立な5軌道の反例とは数えない。
元のsurvival比はこの反例で破れず、slack `16v-7hPrev=38864647022` は大きい。
比への十分条件として選んだ、より強い不等式の反証であり、survival閾値付近の挙動を代表するとは言えない。

候補は `REFUTED`（`E-057`）、係数の再調整をせずこの枝を `STOPPED` にする。
次の作業は最初の反例のphase離脱とblocker birthを分類し、既存runのどの資源が未使用で残るかを
監査すること。新しい不等式は、その分類に未証明の入力が見つかってから一つだけ提案する。

### 最初の反例の原因を分解する診断

0から再実行して697,233行のtraceを出し、全stepと商剰余を別のPython監査で照合した。
最初のlevel-5/4 phaseは31,057対でlowerFreshへ離脱し、level-4/3へ降りてからlate landingに戻る。
開始level qのaddition費用2q+1で数えると、q=0,1,2は各一回（費用1+3+5）、q=3は40,567回
（283,969）、q=4は31,058回（279,522）。総和563,500はexactにv−uと一致した。

prelandingのlevel2 railは `[27689859870,27690136856]`。初めてlevel2へ戻るe−2での値は
27,689,859,868、railの下端より2小さい。`(v-u)-2(e-c)=276988=J+2` なのでrailを避ける条件は
守られている。phaseを跨ぐと、このrailの消費を旧7J/3の費用へ変換できない。
この一例の恒等式を新しい一般定理とはしない。

さらに既存のaccelerated simulatorの監視値だけを差し替えた独立再生で、7個の境界candidateの
first birthを検査した。level3の最初のblocker39,375,735,083はclock11,684,552,030で、
直後のblocker39,375,735,080は11,684,552,036で生まれる。一方、同じlevel5/4 phase末尾の
blocker39,375,641,912はclock7,575,011,311から持ち越されている。fresh return値はe−2が初出だった。
最終値4,318,376,915も一歩ずつのsimulatorと一致した。

これは少数境界の診断であって、全blockerのbirth分類や共同生成の不等式ではない。次のissueでは
`W={3c+v+5−3i : 0≤i≤31057}` 全体を一つの資源集合として分類する。

## 検証・限界・次の判断

- strongest evidence: Q1/Q2とcanonical cutoff反例、具体seedの全stepと一回使用は`PROVED-LEAN`。
  任意finite prefixを含む反例族は`PROVED-PAPER`。
- failed attempts: 自由なeventual floorとrising floor単独の十分性、density/parity/one-useだけによる
  seeded survival比、canonical weighted landing drop（holdoutで5反例）。最初のseedが1を欠く弱さはstress testと一般族で明示的に監査した。
- uncertainty: canonical survival比は未反証・未証明。one-useの有限観測は重み付きbirth budgetを供給しない。
  Chaffinの長距離計算は有限証拠であり、確率や決定的tail boundへ昇格しない。
- next decision: 自由cutoff路線とfinite prefixを追加するだけのseed separatorは停止。
  次は一般countermodel族のLean化と、weighted-drop最初の反例のphase/birth分類。
  新しいsurvival入力には、共同birth生成とphase離脱後に残る資源を扱う定量補題が必要。


## 形式化と引き継ぎの検証結果

`./scripts/check.sh` は全build（259 jobs）、module graph（256 library modules）、direct-import契約、
57行のevidence registry、公理監査1,206宣言を通過。許可公理は `{propext, Classical.choice, Quot.sound}` のみ。
`git diff --check` も通過。検証の抜粋は [validation.txt](data/strategy_2026-09-06/validation.txt)。

変更は新規2 Leanモジュール、root/Audit/import契約、6仮説カード、戦略地図と監査、frontier/台帳/地図/履歴、
8本の探索・解析スクリプトとexact outputs。各コマンドは[再現手順](data/strategy_2026-09-06/README.md)、全変更ファイルは
[changed_files.txt](data/strategy_2026-09-06/changed_files.txt)に記録した。
新規資料は未commit・未pushで、GitHubには[tracker #72](https://github.com/hirokidaichi/recaman-lean-research/issues/72)と
子issue [#70](https://github.com/hirokidaichi/recaman-lean-research/issues/70)、[#71](https://github.com/hirokidaichi/recaman-lean-research/issues/71)を作成した。
