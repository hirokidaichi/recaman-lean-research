import Recaman.LagSevenDonorCoverage

/-!
# OwnerFamilyLagEleven: no lag-11 member in an owner-closed family of short windows

Convention throughout: `past e u d = [e (u-1), e (u-2), ..., e (u-d)]` (newest first),
`true` = A (addition), `false` = S (subtraction); bit `j` (0-based) of `past e u d` is the sign
at clock `u - 1 - j` (`past_getD`). `sOffsets w` lists the 1-based offsets of the S bits of `w`.

## Setting

An *owner family* (`OwnerFamily e mem own lag`) is a set `mem` of additions `b` (`e b = true`)
whose windows `past e b (lag b)` are minimal P2 words of lag 3, 7 or 11 (the twenty words of
`ownerWords`), together with a map `own` such that every member owns one subtraction of its own
window (`own b = b - k` for some S offset `k`) and every subtraction inside any member's window
is owned by some member. This is exactly the shape produced by Hall's theorem for a tight subset
`B` of `U` (|N(B)| = |B| with Hall's condition on subsets of `B`): a bijection `B → N(B)`
matching each member to a subtraction of its window. Only the "onto" half of the bijection and
the function-ness of `own` are used; injectivity is not needed. (The derivation of an owner
family from tightness via Hall's theorem, and the lifting of a periodic tight subset to the
integer line, are not part of this module.)

## What is proved

1. `ownerWords_eq`: `ownerWords` is exactly the list of minimal P2 words (P2 with no proper P2
   prefix) of lengths 3, 7 and 11 in the enumeration order of `bitWords` (`decide`).
2. `check_sound`: the certificate checker `check` is sound: if `check fuel cfg cert = true` and
   `cfg` is realized inside an owner family (`Realizes`), then `False`. The checker walks a search
   tree: at a node for an unowned subtraction `sc` of a placed window, every placement of every
   owner word with any of its S offsets on `sc` either conflicts with an already placed bit / an
   already placed member, or is followed by a verified subtree.
3. `checkRoot_*`: for each of the 17 minimal lag-11 words `v` and for `w2 = ASAASAS`, the
   generated certificate passes the checker with `v` as the member at coordinate 64 (`decide`).
4. `no_lag_eleven_member`: an owner family whose windows are minimal P2 words of lag ≤ 11 has no
   member of lag 11; `no_w2_member`: it has no member whose window is `w2`.

## What is not proved

Nothing here concerns tight subsets or Hall's condition directly: the hypotheses are the owner
family axioms, which follow from tightness + Hall's condition by Hall's theorem (not formalized
here). No periodicity is assumed or used. Windows of lag ≥ 15 are outside the family, so the
result is "no lag-11 member when every member has lag ≤ 11", not the full G1.
-/

namespace Recaman.OwnerFamilyLagEleven

open Recaman.LeadingRunSupply (past P2 past_p2_iff)
open Recaman.LagSevenPrefixRigidity (w1 w2 isP2Word)
open Recaman.TwoSSEndpoint (bitWords hasP2Prefix mem_bitWords)
open Recaman.TwoSSLeadingSibling (past_length)
open Recaman.LagSevenDonorCoverage (past_getD hasP2Prefix_eq_false_iff)

/-- The minimal lag-3 word `AAS`. -/
def aas : List Bool := [true, true, false]
/-- Minimal lag-11 word `SSAAAAAASSS` (index 0 in the `bitWords 11` enumeration). -/
def l01 : List Bool := [false, false, true, true, true, true, true, true, false, false, false]
/-- Minimal lag-11 word `SASAAAASASS` (index 1 in the `bitWords 11` enumeration). -/
def l02 : List Bool := [false, true, false, true, true, true, true, false, true, false, false]
/-- Minimal lag-11 word `SAASAASAASS` (index 2 in the `bitWords 11` enumeration). -/
def l03 : List Bool := [false, true, true, false, true, true, false, true, true, false, false]
/-- Minimal lag-11 word `ASSAAASAASS` (index 3 in the `bitWords 11` enumeration). -/
def l04 : List Bool := [true, false, false, true, true, true, false, true, true, false, false]
/-- Minimal lag-11 word `SAAASSAAASS` (index 4 in the `bitWords 11` enumeration). -/
def l05 : List Bool := [false, true, true, true, false, false, true, true, true, false, false]
/-- Minimal lag-11 word `ASASASAAASS` (index 5 in the `bitWords 11` enumeration). -/
def l06 : List Bool := [true, false, true, false, true, false, true, true, true, false, false]
/-- Minimal lag-11 word `SAASAAASSAS` (index 6 in the `bitWords 11` enumeration). -/
def l07 : List Bool := [false, true, true, false, true, true, true, false, false, true, false]
/-- Minimal lag-11 word `ASSAAAASSAS` (index 7 in the `bitWords 11` enumeration). -/
def l08 : List Bool := [true, false, false, true, true, true, true, false, false, true, false]
/-- Minimal lag-11 word `SAAASASASAS` (index 8 in the `bitWords 11` enumeration). -/
def l09 : List Bool := [false, true, true, true, false, true, false, true, false, true, false]
/-- Minimal lag-11 word `ASASAASASAS` (index 9 in the `bitWords 11` enumeration). -/
def l10 : List Bool := [true, false, true, false, true, true, false, true, false, true, false]
/-- Minimal lag-11 word `ASAASSAASAS` (index 10 in the `bitWords 11` enumeration). -/
def l11 : List Bool := [true, false, true, true, false, false, true, true, false, true, false]
/-- Minimal lag-11 word `AAASSSSAAAS` (index 11 in the `bitWords 11` enumeration). -/
def l12 : List Bool := [true, true, true, false, false, false, false, true, true, true, false]
/-- Minimal lag-11 word `SAAASAASSSA` (index 12 in the `bitWords 11` enumeration). -/
def l13 : List Bool := [false, true, true, true, false, true, true, false, false, false, true]
/-- Minimal lag-11 word `ASASAAASSSA` (index 13 in the `bitWords 11` enumeration). -/
def l14 : List Bool := [true, false, true, false, true, true, true, false, false, false, true]
/-- Minimal lag-11 word `ASAAASSSASA` (index 14 in the `bitWords 11` enumeration). -/
def l15 : List Bool := [true, false, true, true, true, false, false, false, true, false, true]
/-- Minimal lag-11 word `AAASSSASASA` (index 15 in the `bitWords 11` enumeration). -/
def l16 : List Bool := [true, true, true, false, false, false, true, false, true, false, true]
/-- Minimal lag-11 word `AAASSASSSAA` (index 16 in the `bitWords 11` enumeration). -/
def l17 : List Bool := [true, true, true, false, false, true, false, false, false, true, true]

/-- The twenty minimal P2 words of lag 3, 7, 11: `AAS`, `w1`, `w2`, then `l01 .. l17`. -/
def ownerWords : List (List Bool) := [aas, w1, w2, l01, l02, l03, l04, l05, l06, l07, l08, l09, l10, l11, l12, l13, l14, l15, l16, l17]

/-- The seventeen minimal lag-11 words. -/
def lagElevenWords : List (List Bool) := [l01, l02, l03, l04, l05, l06, l07, l08, l09, l10, l11, l12, l13, l14, l15, l16, l17]

/-- Boolean minimality: P2 with no proper P2 prefix. -/
def isMinimalP2 (w : List Bool) : Bool := isP2Word w && !hasP2Prefix w

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
/-- `ownerWords` is exactly the list of minimal P2 words of lengths 3, 7, 11. -/
theorem ownerWords_eq :
    ownerWords = (bitWords 3).filter isMinimalP2 ++ (bitWords 7).filter isMinimalP2 ++
      (bitWords 11).filter isMinimalP2 := by
  decide

/-- 1-based offsets (newest first) of the S bits of `w`. -/
def sOffsets (w : List Bool) : List Nat :=
  ((List.range w.length).filter fun j => w.getD j true == false).map (· + 1)

/-- A partial configuration in shifted coordinates (coordinate `c` is clock `t0 + c - 64`). -/
structure Config where
  bits : List (Nat × Bool)
  members : List (Nat × List Bool)
  owned : List (Nat × Nat)

/-- The known sign at coordinate `c`, if any. -/
def bitAt (bits : List (Nat × Bool)) (c : Nat) : Option Bool :=
  match bits.find? (fun p => p.1 == c) with
  | some p => some p.2
  | none => none

/-- `b` does not contradict the known sign at `c`. -/
def agrees (bits : List (Nat × Bool)) (c : Nat) (b : Bool) : Bool :=
  match bitAt bits c with
  | none => true
  | some b' => b' == b

def isMember (cfg : Config) (u : Nat) : Bool := cfg.members.any fun m => m.1 == u
def isOwned (cfg : Config) (sc : Nat) : Bool := cfg.owned.any fun o => o.1 == sc

/-- Placing owner word `w` with its S offset `k` on coordinate `sc` (owner at `u = sc + k`):
`u` is not yet a member (it would own two subtractions), `u` is not a known S bit, and every
window bit agrees with the known bits. -/
def consistent (cfg : Config) (w : List Bool) (k sc : Nat) : Bool :=
  !(isMember cfg (sc + k)) && agrees cfg.bits (sc + k) true &&
    (List.range w.length).all fun j => agrees cfg.bits (sc + k - 1 - j) (w.getD j true)

/-- The configuration after the placement. -/
def extend (cfg : Config) (w : List Bool) (k sc : Nat) : Config :=
  { bits := (sc + k, true) ::
      ((List.range w.length).map fun j => (sc + k - 1 - j, w.getD j true)) ++ cfg.bits
    members := (sc + k, w) :: cfg.members
    owned := (sc, sc + k) :: cfg.owned }

/-- Subtraction coordinates inside placed windows that have no owner yet. -/
def needs (cfg : Config) : List Nat :=
  (cfg.members.flatMap fun m => (sOffsets m.2).map fun k => m.1 - k).filter fun sc =>
    !(isOwned cfg sc)

/-- A search-tree certificate: a node names the unowned subtraction it expands and, for every
placement `(word index, S offset)` that is consistent, a subtree. -/
inductive Cert where
  | node (sc : Nat) (kids : List (Nat × Nat × Cert))

def findKid (kids : List (Nat × Nat × Cert)) (i k : Nat) : Option Cert :=
  match kids.find? (fun t => t.1 == i && t.2.1 == k) with
  | some t => some t.2.2
  | none => none

/-- The certificate checker. At a node `sc`: `sc` must be an unowned subtraction of a placed
window; for every owner word (index `i`) and every S offset `k` of it, the owner coordinate
`sc + k` must be at least the word length (so that window coordinates are exact), and either the
placement is inconsistent or the certificate supplies a subtree that checks after `extend`. -/
def check : Nat → Config → Cert → Bool
  | 0, _, _ => false
  | fuel + 1, cfg, .node sc kids =>
    (needs cfg).elem sc &&
      (List.range ownerWords.length).all fun i =>
        let w := ownerWords.getD i []
        (sOffsets w).all fun k =>
          decide (w.length ≤ sc + k) &&
            (!(consistent cfg w k sc) ||
              match findKid kids i k with
              | none => false
              | some t => check fuel (extend cfg w k sc) t)

/-- The root configuration: `v` is the member at coordinate 64 and owns its S at offset `k`. -/
def rootConfig (v : List Bool) (k : Nat) : Config :=
  { bits := (64, true) :: ((List.range v.length).map fun j => (64 - 1 - j, v.getD j true))
    members := [(64, v)]
    owned := [(64 - k, 64)] }

/-- Root check: for every subtraction `v` may own, the certificate for that choice passes. -/
def checkRoot (v : List Bool) (certs : List (Nat × Cert)) : Bool :=
  (sOffsets v).all fun k =>
    match certs.find? (fun t => t.1 == k) with
    | none => false
    | some t => check 32 (rootConfig v k) t.2

/-- Certificate for `SSAAAAAASSS`: one search tree per subtraction that `v` may own. -/
def cert_l01 : List (Nat × Cert) := [(1, .node 54 [(14, 5, .node 53 []), (18, 5, .node 53 [])]), (2, .node 54 [(14, 5, .node 53 []), (18, 5, .node 53 [])]), (9, .node 54 [(14, 5, .node 53 []), (18, 5, .node 53 [])]), (10, .node 53 [(14, 6, .node 52 []), (18, 6, .node 55 [(0, 3, .node 51 [(4, 1, .node 49 [])])])]), (11, .node 54 [(14, 5, .node 52 []), (18, 5, .node 55 [(0, 3, .node 51 [(4, 1, .node 49 [])])])])]
/-- Certificate for `SASAAAASASS`: one search tree per subtraction that `v` may own. -/
def cert_l02 : List (Nat × Cert) := [(1, .node 56 [(0, 3, .node 54 [(3, 1, .node 53 [])])]), (3, .node 56 [(0, 3, .node 54 [(3, 1, .node 53 [])])]), (8, .node 54 [(3, 1, .node 53 [])]), (10, .node 56 [(0, 3, .node 53 [(3, 2, .node 45 [(14, 5, .node 44 []), (18, 5, .node 44 [])])])]), (11, .node 56 [(0, 3, .node 54 [(3, 1, .node 45 [(14, 5, .node 44 []), (18, 5, .node 44 [])])])])]
/-- Certificate for `SAASAASAASS`: one search tree per subtraction that `v` may own. -/
def cert_l03 : List (Nat × Cert) := [(1, .node 60 []), (4, .node 57 [(13, 2, .node 54 [])]), (7, .node 60 []), (10, .node 60 []), (11, .node 60 [])]
/-- Certificate for `ASSAAASAASS`: one search tree per subtraction that `v` may own. -/
def cert_l04 : List (Nat × Cert) := [(2, .node 57 [(0, 3, .node 54 [(3, 1, .node 53 []), (6, 2, .node 53 []), (10, 2, .node 53 []), (13, 5, .node 53 [])]), (13, 2, .node 54 [])]), (3, .node 57 [(0, 3, .node 54 [(3, 1, .node 53 []), (6, 2, .node 53 []), (10, 2, .node 53 []), (13, 5, .node 53 [])]), (13, 2, .node 54 [])]), (7, .node 54 [(3, 1, .node 53 []), (6, 2, .node 53 []), (10, 2, .node 53 []), (13, 5, .node 53 [])]), (10, .node 57 [(0, 3, .node 53 [(3, 2, .node 45 [(14, 5, .node 44 []), (18, 5, .node 44 [])]), (6, 3, .node 49 [(0, 3, .node 46 [(3, 1, .node 45 []), (6, 2, .node 45 []), (10, 2, .node 45 []), (13, 5, .node 45 [])]), (13, 2, .node 46 [])]), (10, 3, .node 47 [(19, 5, .node 45 [])]), (13, 6, .node 50 [(4, 1, .node 48 []), (8, 2, .node 48 []), (12, 2, .node 48 []), (16, 2, .node 48 [])])]), (13, 2, .node 53 [])]), (11, .node 57 [(0, 3, .node 54 [(3, 1, .node 45 [(14, 5, .node 44 []), (18, 5, .node 44 [])]), (6, 2, .node 49 [(0, 3, .node 46 [(3, 1, .node 45 []), (6, 2, .node 45 []), (10, 2, .node 45 []), (13, 5, .node 45 [])]), (13, 2, .node 46 [])]), (10, 2, .node 47 [(19, 5, .node 45 [])]), (13, 5, .node 50 [(4, 1, .node 48 []), (8, 2, .node 48 []), (12, 2, .node 48 []), (16, 2, .node 48 [])])]), (13, 2, .node 54 [])])]
/-- Certificate for `SAAASSAAASS`: one search tree per subtraction that `v` may own. -/
def cert_l05 : List (Nat × Cert) := [(1, .node 58 [(8, 11, .node 59 [(0, 3, .node 53 [(3, 2, .node 54 [(0, 3, .node 45 [(14, 5, .node 44 []), (18, 5, .node 44 [])])]), (6, 3, .node 54 [(0, 3, .node 49 [(0, 3, .node 65 [(2, 7, .node 67 []), (12, 9, .node 67 []), (13, 11, .node 67 [])]), (13, 2, .node 46 [])])]), (10, 3, .node 54 [(0, 3, .node 47 [(19, 5, .node 45 [])])])])])]), (5, .node 58 [(8, 11, .node 63 [(12, 11, .node 67 [])])]), (6, .node 59 [(0, 3, .node 53 [(3, 2, .node 54 [(0, 3, .node 45 [(14, 5, .node 44 []), (18, 5, .node 44 [])])]), (6, 3, .node 54 [(0, 3, .node 49 [(0, 3, .node 46 [(3, 1, .node 45 []), (6, 2, .node 45 []), (10, 2, .node 45 []), (13, 5, .node 45 [])]), (13, 2, .node 46 [])])]), (10, 3, .node 54 [(0, 3, .node 47 [(19, 5, .node 45 [])])])]), (8, 10, .node 63 [(12, 11, .node 67 [])])]), (10, .node 58 [(8, 11, .node 63 [(12, 11, .node 67 [])])]), (11, .node 58 [(8, 11, .node 63 [(12, 11, .node 67 [])])])]
/-- Certificate for `ASASASAAASS`: one search tree per subtraction that `v` may own. -/
def cert_l06 : List (Nat × Cert) := [(2, .node 58 [(7, 1, .node 53 []), (12, 11, .node 60 [])]), (4, .node 58 [(7, 1, .node 53 []), (12, 11, .node 62 [])]), (6, .node 60 [(2, 7, .node 62 []), (12, 9, .node 62 []), (13, 11, .node 62 [])]), (10, .node 58 [(7, 1, .node 53 []), (12, 11, .node 62 [])]), (11, .node 58 [(7, 1, .node 54 [(0, 3, .node 60 [(2, 7, .node 62 []), (12, 9, .node 62 []), (13, 11, .node 62 [])])]), (12, 11, .node 62 [])])]
/-- Certificate for `SAASAAASSAS`: one search tree per subtraction that `v` may own. -/
def cert_l07 : List (Nat × Cert) := [(1, .node 60 []), (4, .node 55 []), (8, .node 60 []), (9, .node 60 []), (11, .node 60 [])]
/-- Certificate for `ASSAAAASSAS`: one search tree per subtraction that `v` may own. -/
def cert_l08 : List (Nat × Cert) := [(2, .node 55 [(19, 5, .node 53 [])]), (3, .node 55 [(19, 5, .node 53 [])]), (8, .node 55 [(19, 5, .node 53 [])]), (9, .node 56 [(0, 3, .node 61 [(1, 7, .node 62 [(0, 3, .node 53 [(1, 1, .node 47 [(3, 2, .node 48 [(0, 3, .node 39 [(14, 5, .node 38 []), (18, 5, .node 38 [])])]), (6, 3, .node 48 [(0, 3, .node 43 [(0, 3, .node 40 [(3, 1, .node 39 []), (6, 2, .node 39 []), (10, 2, .node 39 []), (13, 5, .node 39 [])]), (13, 2, .node 40 [])])]), (10, 3, .node 48 [(0, 3, .node 41 [(19, 5, .node 39 [])])]), (14, 5, .node 46 []), (18, 5, .node 46 []), (19, 5, .node 45 [])]), (3, 1, .node 52 []), (4, 1, .node 51 []), (5, 1, .node 50 []), (7, 1, .node 48 []), (9, 1, .node 50 []), (11, 1, .node 47 []), (15, 1, .node 46 []), (19, 7, .node 52 [])])]), (5, 11, .node 62 []), (6, 11, .node 62 []), (7, 11, .node 62 [(0, 3, .node 66 [(8, 11, .node 71 [(12, 11, .node 75 [])])])]), (8, 11, .node 62 [(0, 3, .node 66 [(12, 11, .node 70 [])])])]), (19, 4, .node 53 [])]), (11, .node 55 [(19, 5, .node 52 [])])]
/-- Certificate for `SAAASASASAS`: one search tree per subtraction that `v` may own. -/
def cert_l09 : List (Nat × Cert) := [(1, .node 57 []), (5, .node 57 []), (7, .node 59 [(0, 3, .node 55 [(4, 1, .node 53 [])])]), (9, .node 57 []), (11, .node 57 [])]
/-- Certificate for `ASASAASASAS`: one search tree per subtraction that `v` may own. -/
def cert_l10 : List (Nat × Cert) := [(2, .node 57 [(8, 2, .node 55 [])]), (4, .node 57 [(8, 2, .node 55 [])]), (7, .node 60 [(2, 7, .node 62 []), (13, 11, .node 62 [])]), (9, .node 57 [(8, 2, .node 53 [(7, 1, .node 48 [])])]), (11, .node 57 [(8, 2, .node 55 [])])]
/-- Certificate for `ASAASSAASAS`: one search tree per subtraction that `v` may own. -/
def cert_l11 : List (Nat × Cert) := [(2, .node 59 [(5, 10, .node 58 []), (6, 10, .node 58 [])]), (5, .node 58 [(5, 11, .node 62 []), (6, 11, .node 62 [(0, 3, .node 55 [(4, 1, .node 53 []), (8, 2, .node 53 []), (12, 2, .node 53 []), (16, 2, .node 53 [])])])]), (6, .node 59 [(5, 10, .node 62 []), (6, 10, .node 62 [(0, 3, .node 55 [(4, 1, .node 53 []), (8, 2, .node 53 []), (12, 2, .node 53 []), (16, 2, .node 53 [])])])]), (9, .node 59 [(5, 10, .node 62 []), (6, 10, .node 58 [])]), (11, .node 59 [(5, 10, .node 62 []), (6, 10, .node 58 [])])]
/-- Certificate for `AAASSSSAAAS`: one search tree per subtraction that `v` may own. -/
def cert_l12 : List (Nat × Cert) := [(4, .node 57 []), (5, .node 57 []), (6, .node 57 []), (7, .node 58 [(3, 11, .node 59 [])]), (11, .node 57 [])]
/-- Certificate for `SAAASAASSSA`: one search tree per subtraction that `v` may own. -/
def cert_l13 : List (Nat × Cert) := [(1, .node 56 []), (5, .node 56 []), (8, .node 55 []), (9, .node 56 []), (10, .node 56 [])]
/-- Certificate for `ASASAAASSSA`: one search tree per subtraction that `v` may own. -/
def cert_l14 : List (Nat × Cert) := [(2, .node 55 []), (4, .node 55 []), (8, .node 55 []), (9, .node 54 []), (10, .node 55 [])]
/-- Certificate for `ASAAASSSASA`: one search tree per subtraction that `v` may own. -/
def cert_l15 : List (Nat × Cert) := [(2, .node 57 []), (6, .node 57 []), (7, .node 56 []), (8, .node 57 []), (10, .node 57 [])]
/-- Certificate for `AAASSSASASA`: one search tree per subtraction that `v` may own. -/
def cert_l16 : List (Nat × Cert) := [(4, .node 58 [(3, 11, .node 59 [])]), (5, .node 58 [(3, 11, .node 60 [(0, 3, .node 56 [(4, 1, .node 54 [])])])]), (6, .node 56 [(4, 1, .node 54 [])]), (8, .node 58 [(3, 11, .node 59 [])]), (10, .node 58 [(3, 11, .node 59 [])])]
/-- Certificate for `AAASSASSSAA`: one search tree per subtraction that `v` may own. -/
def cert_l17 : List (Nat × Cert) := [(4, .node 56 []), (5, .node 56 []), (7, .node 56 []), (8, .node 55 []), (9, .node 56 [])]
/-- Certificate for `ASAASAS`: one search tree per subtraction that `v` may own. -/
def cert_w2 : List (Nat × Cert) := [(2, .node 59 [(4, 1, .node 57 []), (8, 2, .node 57 []), (12, 2, .node 57 []), (16, 2, .node 57 [])]), (5, .node 62 [(0, 3, .node 57 [(1, 1, .node 51 [(3, 2, .node 52 [(0, 3, .node 43 [(14, 5, .node 42 []), (18, 5, .node 42 [])])]), (6, 3, .node 52 [(0, 3, .node 47 [(0, 3, .node 44 [(3, 1, .node 43 []), (6, 2, .node 43 []), (10, 2, .node 43 []), (13, 5, .node 43 [])]), (13, 2, .node 44 [])])]), (10, 3, .node 52 [(0, 3, .node 45 [(19, 5, .node 43 [])])]), (14, 5, .node 50 []), (18, 5, .node 50 []), (19, 5, .node 49 [])]), (3, 1, .node 56 []), (4, 1, .node 55 []), (4, 3, .node 52 [(0, 3, .node 50 [(3, 1, .node 49 [])])]), (5, 1, .node 54 []), (7, 1, .node 52 []), (8, 4, .node 55 [(7, 1, .node 50 [])]), (9, 1, .node 54 []), (11, 1, .node 51 []), (12, 4, .node 54 [(8, 2, .node 52 [])]), (15, 1, .node 50 []), (16, 4, .node 52 [])]), (14, 11, .node 66 [])]), (7, .node 62 [(0, 3, .node 59 [(4, 1, .node 52 [(0, 3, .node 50 [(3, 1, .node 49 [])])]), (8, 2, .node 55 [(7, 1, .node 50 [])]), (12, 2, .node 54 [(8, 2, .node 52 [])]), (16, 2, .node 52 [])]), (14, 11, .node 66 [])])]

set_option maxRecDepth 100000 in
theorem checkRoot_l01 : checkRoot l01 cert_l01 = true := by decide
theorem checkRoot_l02 : checkRoot l02 cert_l02 = true := by decide
theorem checkRoot_l03 : checkRoot l03 cert_l03 = true := by decide
theorem checkRoot_l04 : checkRoot l04 cert_l04 = true := by decide
theorem checkRoot_l05 : checkRoot l05 cert_l05 = true := by decide
theorem checkRoot_l06 : checkRoot l06 cert_l06 = true := by decide
theorem checkRoot_l07 : checkRoot l07 cert_l07 = true := by decide
theorem checkRoot_l08 : checkRoot l08 cert_l08 = true := by decide
theorem checkRoot_l09 : checkRoot l09 cert_l09 = true := by decide
theorem checkRoot_l10 : checkRoot l10 cert_l10 = true := by decide
theorem checkRoot_l11 : checkRoot l11 cert_l11 = true := by decide
theorem checkRoot_l12 : checkRoot l12 cert_l12 = true := by decide
theorem checkRoot_l13 : checkRoot l13 cert_l13 = true := by decide
theorem checkRoot_l14 : checkRoot l14 cert_l14 = true := by decide
theorem checkRoot_l15 : checkRoot l15 cert_l15 = true := by decide
theorem checkRoot_l16 : checkRoot l16 cert_l16 = true := by decide
theorem checkRoot_l17 : checkRoot l17 cert_l17 = true := by decide
theorem checkRoot_w2 : checkRoot w2 cert_w2 = true := by decide

/-! ## Semantics of the checker -/

/-- Clock of coordinate `c` relative to the base clock `t0` (the root member sits at coordinate 64). -/
def clock (t0 : Int) (c : Nat) : Int := t0 + (c : Int) - 64

/-- An owner family: members are additions whose windows are among `ownerWords`, each member owns
one subtraction of its own window, and every subtraction inside any member's window is owned by
some member (the "onto" half of the perfect matching that Hall's theorem gives a tight subset). -/
structure OwnerFamily (e : Int → Bool) (mem : Int → Prop) (own : Int → Int) (lag : Int → Nat) :
    Prop where
  window : ∀ b, mem b → past e b (lag b) ∈ ownerWords
  addA : ∀ b, mem b → e b = true
  own_mem : ∀ b, mem b → ∃ k ∈ sOffsets (past e b (lag b)), own b = b - (k : Int)
  onto : ∀ b, mem b → ∀ k ∈ sOffsets (past e b (lag b)), ∃ b', mem b' ∧ own b' = b - (k : Int)

/-- `cfg` is realized inside the family at base clock `t0`: every known bit is the sign of `e`
at its clock, every placed member is a member with that window word and a coordinate at least
its word length (so window coordinates are exact), every recorded ownership holds for `own`,
and every placed member owns something recorded. -/
structure Realizes (e : Int → Bool) (mem : Int → Prop) (own : Int → Int) (lag : Int → Nat)
    (t0 : Int) (cfg : Config) : Prop where
  bits : ∀ p ∈ cfg.bits, e (clock t0 p.1) = p.2
  members : ∀ m ∈ cfg.members,
    mem (clock t0 m.1) ∧ past e (clock t0 m.1) (lag (clock t0 m.1)) = m.2 ∧ m.2.length ≤ m.1
  owned : ∀ o ∈ cfg.owned, own (clock t0 o.2) = clock t0 o.1
  member_owns : ∀ m ∈ cfg.members, ∃ o ∈ cfg.owned, o.2 = m.1

/-- `k ∈ sOffsets w` iff `k` is a 1-based offset inside `w` whose bit is S. -/
theorem sOffsets_mem (w : List Bool) (k : Nat) :
    k ∈ sOffsets w ↔ 1 ≤ k ∧ k ≤ w.length ∧ w.getD (k - 1) true = false := by
  unfold sOffsets
  simp only [List.mem_map, List.mem_filter, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨j, ⟨hj, hw⟩, rfl⟩
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.add_sub_cancel]
    exact hw
  · rintro ⟨h1, h2, h3⟩
    exact ⟨k - 1, ⟨by omega, h3⟩, by omega⟩

/-- A coordinate in `needs cfg` is an unowned subtraction of some placed member's window. -/
theorem needs_spec (cfg : Config) (sc : Nat) (h : sc ∈ needs cfg) :
    (∃ m ∈ cfg.members, ∃ k ∈ sOffsets m.2, sc = m.1 - k) ∧ isOwned cfg sc = false := by
  unfold needs at h
  simp only [List.mem_filter, List.mem_flatMap, List.mem_map, Bool.not_eq_true'] at h
  obtain ⟨⟨m, hm, k, hk, rfl⟩, hown⟩ := h
  exact ⟨⟨m, hm, k, hk, rfl⟩, hown⟩

/-- A known sign found by `bitAt` is an entry of the bit list. -/
theorem bitAt_some (bits : List (Nat × Bool)) (c : Nat) (b : Bool) (h : bitAt bits c = some b) :
    (c, b) ∈ bits := by
  unfold bitAt at h
  split at h
  · rename_i p hp
    have hmem := List.mem_of_find?_eq_some hp
    have hpc := List.find?_some hp
    rw [Option.some.injEq] at h
    simp only [beq_iff_eq] at hpc
    rw [← hpc, ← h]
    exact hmem
  · cases h

/-- A recorded ownership entry makes its subtraction owned. -/
theorem isOwned_of_mem (cfg : Config) (o : Nat × Nat) (ho : o ∈ cfg.owned) :
    isOwned cfg o.1 = true := by
  unfold isOwned
  rw [List.any_eq_true]
  exact ⟨o, ho, beq_self_eq_true o.1⟩

/-- If every known bit is the sign of `e` at its clock, then the actual sign of `e` at a
coordinate agrees with the known bits. -/
theorem agrees_of_bits (bits : List (Nat × Bool)) (e : Int → Bool) (t0 : Int)
    (hbits : ∀ p ∈ bits, e (clock t0 p.1) = p.2) (c : Nat) (b : Bool)
    (hb : e (clock t0 c) = b) : agrees bits c b = true := by
  unfold agrees
  split
  · rfl
  · rename_i b0 hb0
    have h0 : e (clock t0 c) = b0 := hbits (c, b0) (bitAt_some bits c b0 hb0)
    exact beq_iff_eq.mpr (h0.symm.trans hb)

/-- Soundness of the checker: a passing certificate refutes every realization of its
configuration inside an owner family. -/
theorem check_sound (e : Int → Bool) (mem : Int → Prop) (own : Int → Int) (lag : Int → Nat)
    (hF : OwnerFamily e mem own lag) (t0 : Int) :
    ∀ (fuel : Nat) (cfg : Config) (cert : Cert),
      check fuel cfg cert = true → Realizes e mem own lag t0 cfg → False := by
  intro fuel
  induction fuel with
  | zero =>
    intro cfg cert h _
    rw [check] at h
    exact absurd h (by decide)
  | succ fuel ih =>
    intro cfg cert h hR
    obtain ⟨sc, kids⟩ := cert
    rw [check, Bool.and_eq_true, List.elem_iff, List.all_eq_true] at h
    obtain ⟨hneed, hall⟩ := h
    -- `sc` is an unowned subtraction of the placed member `m`
    obtain ⟨⟨m, hm, k0, hk0, hsc⟩, hunowned⟩ := needs_spec cfg sc hneed
    obtain ⟨hmemb, hwin, hlenm⟩ := hR.members m hm
    obtain ⟨_, hk0b, _⟩ := (sOffsets_mem _ k0).mp hk0
    have hclock_sc : clock t0 sc = clock t0 m.1 - (k0 : Int) := by
      unfold clock; omega
    -- the family supplies an owner `b'` of that subtraction
    obtain ⟨b', hmemb', hownb'⟩ :=
      hF.onto (clock t0 m.1) hmemb k0 (by rw [hwin]; exact hk0)
    rw [← hclock_sc] at hownb'
    obtain ⟨w', hw'⟩ : ∃ w', past e b' (lag b') = w' := ⟨_, rfl⟩
    have hw'len : w'.length = lag b' := by rw [← hw', past_length]
    have hw'get : ∀ j, j < w'.length → w'.getD j true = e (b' - 1 - (j : Int)) := by
      intro j hj
      rw [← hw', past_getD e b' (lag b') j (by omega)]
    have hwin' : w' ∈ ownerWords := by
      have := hF.window b' hmemb'
      rwa [hw'] at this
    obtain ⟨k', hk', hownk'⟩ := hF.own_mem b' hmemb'
    rw [hw'] at hk'
    have hb'eq : b' = clock t0 (sc + k') := by
      have h1 : own b' = t0 + (sc : Int) - 64 := hownb'
      unfold clock; omega
    subst hb'eq
    -- the checker examined the placement of `w'` with offset `k'` on `sc`
    obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hwin'
    have hgetD : ownerWords.getD i [] = w' := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hgi]
    have hi' := hall i (List.mem_range.mpr hi)
    simp only [hgetD, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
      at hi'
    obtain ⟨hlen', hrest⟩ := hi' k' hk'
    have hclock_j : ∀ j, j < w'.length →
        clock t0 (sc + k' - 1 - j) = clock t0 (sc + k') - 1 - (j : Int) := by
      intro j hj
      unfold clock; omega
    -- the placement is consistent with `cfg`
    have hcons : consistent cfg w' k' sc = true := by
      unfold consistent
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · unfold isMember
        rw [List.any_eq_false]
        intro m' hm' hcontra
        simp only [beq_iff_eq] at hcontra
        obtain ⟨o, ho, ho2⟩ := hR.member_owns m' hm'
        have hoo := hR.owned o ho
        rw [ho2, hcontra, hownb'] at hoo
        have ho1 : o.1 = sc := by unfold clock at hoo; omega
        have hsc_owned := isOwned_of_mem cfg o ho
        rw [ho1, hunowned] at hsc_owned
        exact absurd hsc_owned (by decide)
      · exact agrees_of_bits cfg.bits e t0 hR.bits (sc + k') true (hF.addA _ hmemb')
      · intro j hj
        apply agrees_of_bits cfg.bits e t0 hR.bits
        rw [hw'get j hj, hclock_j j hj]
    -- the extended configuration is realized as well
    have hRext : Realizes e mem own lag t0 (extend cfg w' k' sc) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro p hp
        simp only [extend, List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hp
        rcases hp with (rfl | ⟨j, hj, rfl⟩) | hp
        · exact hF.addA _ hmemb'
        · show e (clock t0 (sc + k' - 1 - j)) = w'.getD j true
          rw [hclock_j j hj, hw'get j hj]
        · exact hR.bits p hp
      · intro m' hm'
        simp only [extend, List.mem_cons] at hm'
        rcases hm' with rfl | hm'
        · exact ⟨hmemb', hw', hlen'⟩
        · exact hR.members m' hm'
      · intro o ho
        simp only [extend, List.mem_cons] at ho
        rcases ho with rfl | ho
        · exact hownb'
        · exact hR.owned o ho
      · intro m' hm'
        simp only [extend, List.mem_cons] at hm'
        rcases hm' with rfl | hm'
        · refine ⟨(sc, sc + k'), ?_, rfl⟩
          show (sc, sc + k') ∈ (sc, sc + k') :: cfg.owned
          exact List.mem_cons.mpr (Or.inl rfl)
        · obtain ⟨o, ho, ho2⟩ := hR.member_owns m' hm'
          refine ⟨o, ?_, ho2⟩
          show o ∈ (sc, sc + k') :: cfg.owned
          exact List.mem_cons.mpr (Or.inr ho)
    -- so the certificate must supply a verified subtree, which the induction hypothesis refutes
    rcases hrest with hbad | hok
    · rw [hcons] at hbad
      exact absurd hbad (by decide)
    · split at hok
      · exact absurd hok (by decide)
      · exact ih _ _ hok hRext

/-- The root configuration is realized by a member `t0` with window `v` owning its S at
offset `k`. -/
theorem rootConfig_realizes (e : Int → Bool) (mem : Int → Prop) (own : Int → Int)
    (lag : Int → Nat) (hF : OwnerFamily e mem own lag) (t0 : Int) (v : List Bool) (k : Nat)
    (hmem : mem t0) (hv : past e t0 (lag t0) = v) (hlen : v.length ≤ 64) (hk : k ∈ sOffsets v)
    (hown : own t0 = t0 - (k : Int)) : Realizes e mem own lag t0 (rootConfig v k) := by
  have hlag : v.length = lag t0 := by rw [← hv, past_length]
  have hc64 : clock t0 64 = t0 := by unfold clock; omega
  obtain ⟨_, hkb, _⟩ := (sOffsets_mem v k).mp hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [rootConfig, List.mem_cons, List.mem_map, List.mem_range] at hp
    rcases hp with rfl | ⟨j, hj, rfl⟩
    · show e (clock t0 64) = true
      rw [hc64]
      exact hF.addA t0 hmem
    · show e (clock t0 (64 - 1 - j)) = v.getD j true
      rw [← hv, past_getD e t0 (lag t0) j (by omega)]
      congr 1
      unfold clock; omega
  · intro m hm
    simp only [rootConfig, List.mem_singleton] at hm
    subst hm
    refine ⟨?_, ?_, hlen⟩
    · show mem (clock t0 64)
      rw [hc64]; exact hmem
    · show past e (clock t0 64) (lag (clock t0 64)) = v
      rw [hc64]; exact hv
  · intro o ho
    simp only [rootConfig, List.mem_singleton] at ho
    subst ho
    show own (clock t0 64) = clock t0 (64 - k)
    rw [hc64, hown]
    unfold clock; omega
  · intro m hm
    simp only [rootConfig, List.mem_singleton] at hm
    subst hm
    refine ⟨(64 - k, 64), ?_, rfl⟩
    show (64 - k, 64) ∈ [(64 - k, 64)]
    exact List.mem_singleton.mpr rfl

/-- Soundness of the root check: a passing root certificate for `v` refutes every member of an
owner family whose window is `v` (of length at most 64). -/
theorem checkRoot_sound (e : Int → Bool) (mem : Int → Prop) (own : Int → Int) (lag : Int → Nat)
    (hF : OwnerFamily e mem own lag) (v : List Bool) (certs : List (Nat × Cert))
    (hc : checkRoot v certs = true) (t0 : Int) (hmem : mem t0) (hv : past e t0 (lag t0) = v)
    (hlen : v.length ≤ 64) : False := by
  obtain ⟨k, hk, hown⟩ := hF.own_mem t0 hmem
  rw [hv] at hk
  unfold checkRoot at hc
  rw [List.all_eq_true] at hc
  have hk' := hc k hk
  split at hk'
  · exact absurd hk' (by decide)
  · rename_i t _
    exact check_sound e mem own lag hF t0 32 (rootConfig v k) t.2 hk'
      (rootConfig_realizes e mem own lag hF t0 v k hmem hv hlen hk hown)

/-- Every owner word of length 11 is one of the seventeen minimal lag-11 words. -/
theorem lag_eleven_window_mem (w : List Bool) (hw : w ∈ ownerWords) (hlen : w.length = 11) :
    w ∈ lagElevenWords := by
  have key : ∀ w ∈ ownerWords, w.length = 11 → w ∈ lagElevenWords := by decide
  exact key w hw hlen

/-- **Main theorem.** An owner family (windows among the minimal P2 words of lag 3, 7, 11) has
no member of lag 11. -/
theorem no_lag_eleven_member (e : Int → Bool) (mem : Int → Prop) (own : Int → Int)
    (lag : Int → Nat) (hF : OwnerFamily e mem own lag) (t0 : Int) (hmem : mem t0)
    (hlag : lag t0 = 11) : False := by
  have hw := hF.window t0 hmem
  have hlen : (past e t0 (lag t0)).length = 11 := by rw [past_length, hlag]
  have h17 := lag_eleven_window_mem _ hw hlen
  simp only [lagElevenWords, List.mem_cons, List.not_mem_nil, or_false] at h17
  rcases h17 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact checkRoot_sound e mem own lag hF _ _ checkRoot_l01 t0 hmem h (by decide)
  · exact checkRoot_sound e mem own lag hF _ _ checkRoot_l02 t0 hmem h (by decide)
  · exact checkRoot_sound e mem own lag hF _ _ checkRoot_l03 t0 hmem h (by decide)
  · exact checkRoot_sound e mem own lag hF _ _ checkRoot_l04 t0 hmem h (by decide)
  · exact checkRoot_sound e mem own lag hF _ _ checkRoot_l05 t0 hmem h (by decide)
  · exact checkRoot_sound e mem own lag hF _ _ checkRoot_l06 t0 hmem h (by decide)
  · exact checkRoot_sound e mem own lag hF _ _ checkRoot_l07 t0 hmem h (by decide)
  · exact checkRoot_sound e mem own lag hF _ _ checkRoot_l08 t0 hmem h (by decide)
  · exact checkRoot_sound e mem own lag hF _ _ checkRoot_l09 t0 hmem h (by decide)
  · exact checkRoot_sound e mem own lag hF _ _ checkRoot_l10 t0 hmem h (by decide)
  · exact checkRoot_sound e mem own lag hF _ _ checkRoot_l11 t0 hmem h (by decide)
  · exact checkRoot_sound e mem own lag hF _ _ checkRoot_l12 t0 hmem h (by decide)
  · exact checkRoot_sound e mem own lag hF _ _ checkRoot_l13 t0 hmem h (by decide)
  · exact checkRoot_sound e mem own lag hF _ _ checkRoot_l14 t0 hmem h (by decide)
  · exact checkRoot_sound e mem own lag hF _ _ checkRoot_l15 t0 hmem h (by decide)
  · exact checkRoot_sound e mem own lag hF _ _ checkRoot_l16 t0 hmem h (by decide)
  · exact checkRoot_sound e mem own lag hF _ _ checkRoot_l17 t0 hmem h (by decide)

/-- An owner family has no member whose window is `w2 = ASAASAS`. -/
theorem no_w2_member (e : Int → Bool) (mem : Int → Prop) (own : Int → Int) (lag : Int → Nat)
    (hF : OwnerFamily e mem own lag) (t0 : Int) (hmem : mem t0)
    (hv : past e t0 (lag t0) = w2) : False :=
  checkRoot_sound e mem own lag hF w2 cert_w2 checkRoot_w2 t0 hmem hv (by decide)

/-- Semantic form of the main theorem: members are additions of lag 3, 7 or 11 whose windows
are P2 with no proper P2 prefix, each owning a subtraction of its window, with every
subtraction inside a member's window owned by some member; then no member has lag 11. -/
theorem no_lag_eleven_member_of_minimal (e : Int → Bool) (mem : Int → Prop) (own : Int → Int)
    (lag : Int → Nat) (hlag : ∀ b, mem b → lag b = 3 ∨ lag b = 7 ∨ lag b = 11)
    (hP : ∀ b, mem b → P2 (past e b (lag b)))
    (hmin : ∀ b, mem b → ∀ d, d < lag b → 0 < d → ¬ P2 ((past e b (lag b)).take d))
    (haddA : ∀ b, mem b → e b = true)
    (hown : ∀ b, mem b → ∃ k ∈ sOffsets (past e b (lag b)), own b = b - (k : Int))
    (honto : ∀ b, mem b → ∀ k ∈ sOffsets (past e b (lag b)),
      ∃ b', mem b' ∧ own b' = b - (k : Int))
    (t0 : Int) (hmem : mem t0) (h11 : lag t0 = 11) : False := by
  have hF : OwnerFamily e mem own lag := by
    refine ⟨?_, haddA, hown, honto⟩
    intro b hb
    obtain ⟨w, hw⟩ : ∃ w, past e b (lag b) = w := ⟨_, rfl⟩
    have hwlen : w.length = lag b := by rw [← hw, past_length]
    have hP' : P2 w := by rw [← hw]; exact hP b hb
    have hmin' : ∀ d, d < w.length → 0 < d → ¬ P2 (w.take d) := by
      intro d hd
      have := hmin b hb d (by omega)
      rwa [hw] at this
    have hmm : isMinimalP2 w = true := by
      unfold isMinimalP2 isP2Word
      rw [(hasP2Prefix_eq_false_iff w).mpr hmin']
      simp [hP'.1, hP'.2]
    have hbw := mem_bitWords w
    rw [hwlen] at hbw
    rw [hw, ownerWords_eq, List.mem_append, List.mem_append]
    rcases hlag b hb with h | h | h <;> rw [h] at hbw
    · exact Or.inl (Or.inl (List.mem_filter.mpr ⟨hbw, hmm⟩))
    · exact Or.inl (Or.inr (List.mem_filter.mpr ⟨hbw, hmm⟩))
    · exact Or.inr (List.mem_filter.mpr ⟨hbw, hmm⟩)
  exact no_lag_eleven_member e mem own lag hF t0 hmem h11

end Recaman.OwnerFamilyLagEleven
