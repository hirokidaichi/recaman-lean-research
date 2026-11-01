# 制約・探索領域の意味監査

対象は任意の有限符号語。Recamán実軌道を仮定していない。
完成設定Dや全真部分区間IHを、有限solverの制約へ暗黙に加えたとは扱わない。

## exact CP-SAT

- F/Gは±1の実際の歩みとその積分。各候補窓についてmass=1、moment=0の両方をBooleanと同値にした。
- Eは「clockがA、かつ少なくとも一つのP2窓」と同値。存在する窓を都合よく数え落とす選択変数ではない。
- dは整数の#S−#E。ANはAかつ非Endableの個数。clocksを一回数え、窓の本数を数えない。
- 窓長3 mod4への制限は既存Leanのp2_count_identitiesによる必要条件。独立の校正では全始点を直接検査した。
- prefix SAAAを固定したモデルの結果を、任意の古いprefixに対する結果へ拡張しない。
- q0=80のモデルはその固定長だけ。長さ≤80の全域を検査したわけではない。

変数domainは数学的に安全な上界である。

```text
|F(i)| <= i <= N
|G(i)| <= N(N+1)/2
|d(i)| <= i, 0 <= AN(i) <= i
Z for a tail of length L = L - sum_(j=0..L-1) j*sigma(j)
|Z| <= L(L+1)/2 <= N^2
```

Rのhは長さ以内、Yのdropは二点間の長さ以内。積h(h+1)もdomain N(N+1)に収まる。
UNKNOWNのresponseにobjective=0/best_bound=0が出ても、面積下界や反例不在の証拠とは解釈しない。

## E-382の深さ4分類

深さは[k1,b]まで、d/ayは最後の符号を数えたb+1まで。
終点の判定後にF(b+1)が深さを外れる枝を止める。
数学的な語長/S数cutoffはなく、stack guardと時間上限の未使用をcomplete=trueとともに確認した。
個々のendpoint数は最後の符号を含む分岐の数であり、同じprefix状態を一意に数えた統計ではない。

## 共通prefix mass代表を使う有限tail探索

tail長L≤32、d(k1)=0、d(q0)=1とする。ANをtailの非Endable A数として

```text
F(q0)-F(k1) = AN-1 >= -1
L = 2*S + (F(q0)-F(k1))
2*S <= L+1 <= 33  => S<=16
F(b) >= F(k1)-S >= F(k1)-16  (k1<=b<q0)
```

Leanのendable_tail_mass_representativeで、mass≤17の一つのBlockWord prefix代表が全tail Endableを保存する。
必要なold windowがなければ空prefixでよい。massが1/2/4増える文法なので、その有限mass以下の全語を列挙できる。
代表のprefix不足d=0はLean定理の結論ではないため、全代表を実際の窓で別に確認する。
それが通れば、元のd(k1)=0からtailの整数不足が同じになる。元のprefix非負性と代表の非負性も区別して検査する。

探索の追加枝刈りは、S>16、AN>3、内部d<1、残りclock数ではd=1へ戻れない場合のみ。
全tail長1..32を走査するが、32を超すtailの結果は含まない。
小域N=12,R=7で校正後、N=32/R=17も別C++で全125181373 nodeを独立再実行し、全cut数・候補・最小値を含め一致した。全始点の後ろ向きmass/momentと直接面積和を用い、mod4を使わない。Lean証明書化は未完了。

## old spectrum緩和

S_rは実際のBlockWordのmass/area spectrumで、各組に語のwitnessを持つ。
各old flagはその集合に入るが、flagごとに別のprefixを選べる。この緩和のSATは実語の反例ではない。
local P2は全て強制的に数える。old flagで既存のlocal Eを消すことはできない。
持上げではlocal窓のあるclockの冗長flagを消し、必要なold startの最古位置からのBlockWord suffixを列挙する。
共通Endable patternの一致、prefix不足0、prefix非負性を別々に報告する。
未完了の持上げ探索を「持上げ不能」とは扱わない。

## 09:54 brief同期の不具合と修理

CURRENT_FRONTIERの本文は最新だったが、証拠IDの抽出がUnicodeの\bを使い、E-379で/E-381は等の日本語隣接を落としていた。ASCIIのID継続文字だけを境界条件として除外するようdev_tool.pyを修理。日本語隣接の登録/未知ID、ASCII連続IDを回帰に追加。数学的結果とは別の記録・運用監査で、探索CPUを消費しない。make test-toolsとmake briefを再実行する。
