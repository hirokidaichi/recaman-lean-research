# Kernel-accepted experiment: NOT adopted or registered

Exact public signatures of frozen source SHA25648225eee246698de2c5a9348a0fdb8b80e92cfa100ef769124672da79f374f82. This is NOT a G5 audit authorizing adoption, no PROVED-LEAN row, no root/Audit import. E713 already supplies the complete initial-S producer after substitution/shift. Individual kernel acceptance and substance heuristics did not establish novelty. Vacuity helper512MB STOPPED BEFORE any theorem probe; no clean report.

```lean
theorem padded_root_equations (f : Nat → Bool) (r q : Nat) (hr : 1≤r) :
    Win (trimSSequence f 0 r) 0 (r+q) ↔
      Fw f q=(r : Int)+1 ∧
      2*Ar f 0 q=(r : Int)*(2*(q : Int)+r+1) := by
```

```lean
theorem added_source_equations (f : Nat → Bool) (d i q : Nat) (hi : i<d) :
    Win (trimSSequence f 0 d) i (d+q-i) ↔
      Fw f q=((d-i : Nat) : Int)+1 ∧
      2*Ar f 0 q=((d-i : Nat) : Int)*(2*(q : Int)+(d-i : Nat)+1) := by
```

```lean
theorem padded_actual_iff (f : Nat → Bool) (d q : Nat) :
    EndN (trimSSequence f 0 d) 0 (d+q) ↔
      EndN f 0 q ∨ (f q=true ∧ ∃ r : Nat, 1≤r ∧ r≤d ∧
        Fw f q=(r : Int)+1 ∧
        2*Ar f 0 q=(r : Int)*(2*(q : Int)+r+1)) := by
```

```lean
theorem padded_actual_height_iff (f : Nat → Bool) (d q : Nat) :
    EndN (trimSSequence f 0 d) 0 (d+q) ↔
      EndN f 0 q ∨ (f q=true ∧ 2≤Fw f q ∧ Fw f q≤(d : Int)+1 ∧
        2*Ar f 0 q=(Fw f q-1)*(2*(q : Int)+Fw f q)) := by
```

```lean
theorem added_source_unique (f : Nat → Bool) (d i j q : Nat)
    (hi : i<d) (hj : j<d)
    (hI : Win (trimSSequence f 0 d) i (d+q-i))
    (hJ : Win (trimSSequence f 0 d) j (d+q-j)) : i=j := by
```
