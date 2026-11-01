# Joint-birth diagnostic — 2026-09-07

**31,058個のblockerの初出は、arc 39のlevel-5加算runとarc 40のlevel-3減算runの二群に完全分類された。新しい大域不等式は得られず、この診断から正のsurvival証明へ進む枝はSTOPPED。**

#71の分類そのものは完了。結果の証拠レベルは`COMPUTED`（E-058）、継続判断は`STOPPED`（E-059）。
canonical survival比、全射性、非全射性はいずれも未解決である。

## Fixed target and complete birth classification

固定対象はc=11685598221、v=4318940415、J=276986。
W_i=3c+v+5−3i=39375735083−3i、0≤i≤31057。
各W_iはclock c+5+2iのlevel 4→5加算を塞ぐ候補で、全件一度ずつ使われる。

| iの区間 | 個数 | 初出arc / level / 符号 | first-birth clock | 生成rail |
|---|---:|---|---|---|
| 0…25030 | 25,031 | arc 40 / q=3 / S | 11684552030+6i | [39375659993,39376098634] |
| 25031…31057 | 6,027 | arc 39 / q=5 / A | 7575197653−6i | [39375641911,39375659992] |

first-birth時刻の重複は0。共有するのは時刻ではなく、上の二つの生成runである。
古いarc 39のrunはclock7575011308から7575047471までの18,082 SA対で、上側railを供給する。
同じarc 40のrunはclock11683824928から11684702211までの438,642 SA対で、下側railを供給する。
両run内でlevelはそれぞれ4/5、3/4に固定されている。

二つのrailは端点39375659992 / 39375659993で隙間なく接する。
合計456,724値のうち、今回のWが使う値は31,058値、Wに使われない値は425,666値である。
**これはこの消費集合Wに対する差集合**であり、他の時刻の候補に使われていないことや、将来の未消費資源を意味しない。
区間内でもWは3刻みの疎な集合なので、残りを一つの連続未消費区間とみなさない。

次のcandidate W_31058=39375641909は結合railの下端より2小さい。
clock11685660342で実際にfresh subtractionとなり、level 4→3へ離脱する。
従ってこの一例のphase終了は、二つのproducer railを合わせた値域の下端と対応する。
「全canonical phaseが二つのrunで支えられる」という一般命題は提案していない。

## Relation to the later return and failed weight bound

高いphaseを離脱した後の40,566回のlevel 3→4加算のcandidateは、全てprelanding q=2 rail
[27689859870,27690136856]に入る。popup直後のclock c+4の1回はこのrailの外にある。
最後のq=2へのfresh returnはclock11685741475、
値27689859868で、ここでもrail下端より2小さい。

この例の高いphaseの加算回数N=31058、後続の低いphaseの加算回数K=40566とすると、

```text
J+2 = 5N+3K = 276988
v-u = 9N+7K+16 = 563500
e-c = 2N+2K+8 = 143256
3(v-u)-7J = 62-8N = -248402
```

はexact trace上で成立する。これで旧候補の破れ方は説明できるが、これらはphaseの
値・clock・剰余を足し合わせた既知の費用恒等式で、新しい大域制約ではない。
元のsurvival比のslack 16v−7hPrev=38864647022は大きく、この一例は閾値から遠い。
この診断は元の比を反証していない。

## Comparison with the Lean countermodel family

#70 / E-056は、任意の有限Fを含めたseedに対し、実stepが
SS(AS)^J S A^D S^Dを生成し、seed density/range/parityと一回使用を同時に満たしても
survival比を破ることを`PROVED-LEAN`にした。
今回のcanonical例には二つのproducerのactual birthが存在するが、birthの分類だけから
その二つのrunの長さ・配置・残余をc,v,Jへ拘束する不等式は導いていない。
既知のfinite prefixを追加するだけではE-056により不十分である。

## Decision and next gate

分類の受入条件は達成したが、cutoffに依存しない新しい資源不等式は0件。
NやKの係数を調整する案、Wの一回使用だけの案、railのcardinalityだけの案は停止する。
一般補題の量化子や未使用holdoutを凍結する段階には進んでいない。
従って「新候補が未反証」という主張も、Lean wrapperの追加も行わない。

再開には、actual producer群の共同生成から独立に証明でき、E-056の弱履歴族を排除し、
かつsurvival比への依存列の未知入力を一つ減らす具体的な不等式が必要である。
この作業ではその不等式を発見していない。#72では、この停止理由を戦略地図へ反映する。

## Reproduction and validation

[仮説カード](HYPOTHESIS_CARD_2026-09-07_JOINT_BIRTH_DIAGNOSTIC.md)、
[exact dataとコマンド](data/issues_2026-09-07/README.md)を参照。
31,058件はaccelerated observerと独立のscalar observerでfirst-birth clock/signを全件照合した。
生成segmentの閉形式、arc、consumer候補、phase離脱も検査した。計算は一般証明ではない。
