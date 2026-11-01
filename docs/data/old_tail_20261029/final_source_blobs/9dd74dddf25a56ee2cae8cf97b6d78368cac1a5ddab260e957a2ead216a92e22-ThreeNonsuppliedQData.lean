/- Generated from q-certificate.json; SHA256 661268f51756c9137f33f568d8a211e878367cf5fffe252eb78a67830422bd39 -/
import Recaman.ThreeNonsuppliedData

set_option maxRecDepth 100000

namespace Recaman.ThreeNonsuppliedQData

open Recaman.LeadingRunSupply
open Recaman.ThreeNonsuppliedData (wordArea localSupply oldSignature endpointWords decodeWord)

structure State where
  root : List Bool
  word : List Bool
  nonsupplied : Nat
  deriving DecidableEq, Inhabited

def goodState (s : State) : Bool :=
  decide (s.root ∈ endpointWords ∧ s.nonsupplied≤1 ∧ -4≤mass s.word ∧
    1≤mass s.root+1+(s.nonsupplied : Int)-mass s.word ∧
    (mass s.word≤0 → 1≤wordArea s.word+(s.word.length : Int)*(1-mass s.word)))

def stepS (s : State) : Option State :=
  if -4≤mass (s.word++[false]) then some ⟨s.root,s.word++[false],s.nonsupplied⟩ else none

def stepA (s : State) (e : Bool) : Option State :=
  let an := s.nonsupplied+(if e then 0 else 1)
  let w := s.word++[true]
  let admitted := if e then localSupply s.word || oldSignature s.word else !localSupply s.word
  if admitted && decide (an≤1) && decide (1≤mass s.root+1+(an : Int)-mass w) then
    some ⟨s.root,w,an⟩ else none

abbrev Row := Nat × Nat × Nat × Nat

structure Table where
  size : Nat
  get : Nat → Row

def unpack (code : Nat) : State :=
  ⟨endpointWords[code%8]!, decodeWord 20 (code/16), (code/8)%2⟩

def stateAt (rs : Table) (i : Nat) : State := unpack (rs.get i).1

def checkOption (rs : Table) (s : Option State) (j : Nat) : Bool :=
  match s with
  | none => decide (j=0)
  | some t => decide (0<j ∧ j-1<rs.size ∧ stateAt rs (j-1)=t)

def checkOne (rs : Table) (i : Nat) : Bool :=
  let row := rs.get i
  let s := stateAt rs i
  [goodState s, checkOption rs (stepS s) row.2.1,
    checkOption rs (stepA s false) row.2.2.1,
    checkOption rs (stepA s true) row.2.2.2].all id

def verified (rs : Table) : Bool := (List.range rs.size).all (checkOne rs)

def verifiedRange (rs : Table) (lo count : Nat) : Bool :=
  (List.range count).all fun j => checkOne rs (lo+j)

def Member (rs : Table) (s : State) : Prop := ∃ i, i<rs.size ∧ stateAt rs i=s

theorem verifiedRange_at (rs : Table) (lo count : Nat) (h : verifiedRange rs lo count=true)
    (i : Nat) (hlo : lo≤i) (hhi : i<lo+count) : checkOne rs i=true := by
  have ht := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  rwa [Nat.add_sub_cancel' hlo] at ht

theorem row_checked (rs : Table) (h : verified rs=true) (i : Nat) (hi : i<rs.size) :
    checkOne rs i=true := List.all_eq_true.mp h i (List.mem_range.mpr hi)

theorem member_area (rs : Table) (h : verified rs=true) (s : State) (hs : Member rs s)
    (hguard : mass s.word≤0) : 1≤wordArea s.word+(s.word.length : Int)*(1-mass s.word) := by
  obtain ⟨i, hi, rfl⟩ := hs
  have hr := row_checked rs h i hi
  simp only [checkOne, List.all_cons, List.all_nil, id_eq,
    Bool.and_true, Bool.and_eq_true] at hr
  have hg : (stateAt rs i).root ∈ endpointWords ∧ (stateAt rs i).nonsupplied≤1 ∧
      -4≤mass (stateAt rs i).word ∧
      1≤mass (stateAt rs i).root+1+((stateAt rs i).nonsupplied : Int)-mass (stateAt rs i).word ∧
      (mass (stateAt rs i).word≤0 → 1≤wordArea (stateAt rs i).word+
        ((stateAt rs i).word.length : Int)*(1-mass (stateAt rs i).word)) := of_decide_eq_true hr.1
  exact hg.2.2.2.2 hguard

theorem member_stepS (rs : Table) (h : verified rs=true) (s t : State)
    (hs : Member rs s) (ht : stepS s=some t) : Member rs t := by
  obtain ⟨i, hi, rfl⟩ := hs
  have hr := row_checked rs h i hi
  simp only [checkOne, List.all_cons, List.all_nil, id_eq,
    Bool.and_true, Bool.and_eq_true] at hr
  have hc := hr.2.1
  rw [ht] at hc
  have hh := of_decide_eq_true hc
  exact ⟨_,hh.2.1,hh.2.2⟩

theorem member_stepA (rs : Table) (h : verified rs=true) (s t : State) (e : Bool)
    (hs : Member rs s) (ht : stepA s e=some t) : Member rs t := by
  obtain ⟨i, hi, rfl⟩ := hs
  have hr := row_checked rs h i hi
  simp only [checkOne, List.all_cons, List.all_nil, id_eq,
    Bool.and_true, Bool.and_eq_true] at hr
  have hc : checkOption rs (stepA (stateAt rs i) e)
      (if e then (rs.get i).2.2.2 else (rs.get i).2.2.1)=true := by
    cases e
    · exact hr.2.2.1
    · exact hr.2.2.2
  rw [ht] at hc
  have hh := of_decide_eq_true hc
  exact ⟨_,hh.2.1,hh.2.2⟩


def rowAt (i : Nat) : Row :=
  if i < 156 then
    if i < 78 then
      if i < 39 then
        if i < 19 then
          if i < 9 then
            if i < 4 then
              if i < 2 then
                if i < 1 then
                  (32,9,10,0)
                else
                  (81,11,12,0)
              else
                if i < 3 then
                  (178,13,0,0)
                else
                  (627,14,15,0)
            else
              if i < 6 then
                if i < 5 then
                  (1396,16,17,0)
                else
                  (1269,18,19,0)
              else
                if i < 7 then
                  (5078,20,21,0)
                else
                  if i < 8 then
                    (69495,22,23,0)
                  else
                    (64,24,25,0)
          else
            if i < 14 then
              if i < 11 then
                if i < 10 then
                  (88,26,0,0)
                else
                  (161,27,28,0)
              else
                if i < 12 then
                  (185,29,0,0)
                else
                  if i < 13 then
                    (354,30,31,0)
                  else
                    (1251,32,33,0)
            else
              if i < 16 then
                if i < 15 then
                  (1275,34,0,0)
                else
                  (2788,35,36,0)
              else
                if i < 17 then
                  (2812,37,0,0)
                else
                  if i < 18 then
                    (2533,38,0,39)
                  else
                    (2557,40,0,0)
        else
          if i < 29 then
            if i < 24 then
              if i < 21 then
                if i < 20 then
                  (10150,41,42,0)
                else
                  (10174,43,0,0)
              else
                if i < 22 then
                  (138983,44,45,0)
                else
                  if i < 23 then
                    (139007,46,0,0)
                  else
                    (128,47,48,0)
            else
              if i < 26 then
                if i < 25 then
                  (152,49,0,0)
                else
                  (168,50,0,0)
              else
                if i < 27 then
                  (321,51,52,0)
                else
                  if i < 28 then
                    (345,53,0,0)
                  else
                    (361,54,0,0)
          else
            if i < 34 then
              if i < 31 then
                if i < 30 then
                  (706,55,56,0)
                else
                  (730,57,0,0)
              else
                if i < 32 then
                  (2499,58,59,0)
                else
                  if i < 33 then
                    (2523,60,0,0)
                  else
                    (2539,61,0,62)
            else
              if i < 36 then
                if i < 35 then
                  (5572,63,64,0)
                else
                  (5596,65,0,0)
              else
                if i < 37 then
                  (5612,66,0,0)
                else
                  if i < 38 then
                    (5061,67,68,0)
                  else
                    (5077,69,70,0)
      else
        if i < 58 then
          if i < 48 then
            if i < 43 then
              if i < 41 then
                if i < 40 then
                  (5101,71,0,0)
                else
                  (20294,72,73,0)
              else
                if i < 42 then
                  (20318,74,0,0)
                else
                  (20334,75,0,0)
            else
              if i < 45 then
                if i < 44 then
                  (277959,76,77,0)
                else
                  (277983,78,0,0)
              else
                if i < 46 then
                  (277999,79,0,0)
                else
                  if i < 47 then
                    (256,0,80,0)
                  else
                    (280,81,0,0)
          else
            if i < 53 then
              if i < 50 then
                if i < 49 then
                  (296,82,0,0)
                else
                  (328,83,0,0)
              else
                if i < 51 then
                  (641,84,85,0)
                else
                  if i < 52 then
                    (665,86,0,0)
                  else
                    (681,87,0,0)
            else
              if i < 55 then
                if i < 54 then
                  (713,88,0,0)
                else
                  (1410,89,90,0)
              else
                if i < 56 then
                  (1434,91,0,0)
                else
                  if i < 57 then
                    (1450,92,0,0)
                  else
                    (4995,93,94,0)
        else
          if i < 68 then
            if i < 63 then
              if i < 60 then
                if i < 59 then
                  (5019,95,0,0)
                else
                  (5035,96,0,0)
              else
                if i < 61 then
                  (5067,97,0,0)
                else
                  if i < 62 then
                    (5083,98,0,0)
                  else
                    (11140,99,100,0)
            else
              if i < 65 then
                if i < 64 then
                  (11164,101,0,0)
                else
                  (11180,102,0,0)
              else
                if i < 66 then
                  (11212,103,0,0)
                else
                  if i < 67 then
                    (10117,104,105,0)
                  else
                    (10141,106,0,0)
          else
            if i < 73 then
              if i < 70 then
                if i < 69 then
                  (10149,107,108,0)
                else
                  (10173,109,0,0)
              else
                if i < 71 then
                  (10189,110,0,0)
                else
                  if i < 72 then
                    (40582,111,112,0)
                  else
                    (40606,113,0,0)
            else
              if i < 75 then
                if i < 74 then
                  (40622,114,0,0)
                else
                  (40654,115,0,0)
              else
                if i < 76 then
                  (555911,116,117,0)
                else
                  if i < 77 then
                    (555935,118,0,0)
                  else
                    (555951,119,0,0)
    else
      if i < 117 then
        if i < 97 then
          if i < 87 then
            if i < 82 then
              if i < 80 then
                if i < 79 then
                  (555983,120,0,0)
                else
                  (536,121,0,0)
              else
                if i < 81 then
                  (552,122,0,0)
                else
                  (584,123,0,0)
            else
              if i < 84 then
                if i < 83 then
                  (648,124,0,0)
                else
                  (1281,0,125,0)
              else
                if i < 85 then
                  (1305,126,0,0)
                else
                  if i < 86 then
                    (1321,127,0,0)
                  else
                    (1353,128,0,0)
          else
            if i < 92 then
              if i < 89 then
                if i < 88 then
                  (1417,129,0,0)
                else
                  (2818,130,131,0)
              else
                if i < 90 then
                  (2842,132,0,0)
                else
                  if i < 91 then
                    (2858,133,0,0)
                  else
                    (2890,134,0,0)
            else
              if i < 94 then
                if i < 93 then
                  (9987,135,136,0)
                else
                  (10011,137,0,0)
              else
                if i < 95 then
                  (10027,138,0,0)
                else
                  if i < 96 then
                    (10059,139,0,0)
                  else
                    (10123,140,0,0)
        else
          if i < 107 then
            if i < 102 then
              if i < 99 then
                if i < 98 then
                  (10155,141,0,0)
                else
                  (22276,142,143,0)
              else
                if i < 100 then
                  (22300,144,0,0)
                else
                  if i < 101 then
                    (22316,145,0,0)
                  else
                    (22348,146,0,0)
            else
              if i < 104 then
                if i < 103 then
                  (22412,147,0,0)
                else
                  (20229,148,149,0)
              else
                if i < 105 then
                  (20253,150,0,0)
                else
                  if i < 106 then
                    (20269,151,0,0)
                  else
                    (20293,152,153,0)
          else
            if i < 112 then
              if i < 109 then
                if i < 108 then
                  (20317,154,0,0)
                else
                  (20333,155,0,0)
              else
                if i < 110 then
                  (20365,156,0,0)
                else
                  if i < 111 then
                    (81158,157,158,0)
                  else
                    (81182,159,0,0)
            else
              if i < 114 then
                if i < 113 then
                  (81198,160,0,0)
                else
                  (81230,161,0,0)
              else
                if i < 115 then
                  (81294,162,0,0)
                else
                  if i < 116 then
                    (1111815,163,164,0)
                  else
                    (1111839,165,0,0)
      else
        if i < 136 then
          if i < 126 then
            if i < 121 then
              if i < 119 then
                if i < 118 then
                  (1111855,166,0,0)
                else
                  (1111887,167,0,0)
              else
                if i < 120 then
                  (1111951,168,0,0)
                else
                  (1064,0,0,0)
            else
              if i < 123 then
                if i < 122 then
                  (1096,0,0,0)
                else
                  (1160,0,0,0)
              else
                if i < 124 then
                  (1288,0,0,0)
                else
                  if i < 125 then
                    (2585,169,0,0)
                  else
                    (2601,170,0,0)
          else
            if i < 131 then
              if i < 128 then
                if i < 127 then
                  (2633,171,0,0)
                else
                  (2697,172,0,0)
              else
                if i < 129 then
                  (2825,173,0,0)
                else
                  if i < 130 then
                    (5634,0,174,0)
                  else
                    (5658,175,0,0)
            else
              if i < 133 then
                if i < 132 then
                  (5674,176,0,0)
                else
                  (5706,177,0,0)
              else
                if i < 134 then
                  (5770,178,0,0)
                else
                  if i < 135 then
                    (19971,0,179,0)
                  else
                    (19995,180,0,0)
        else
          if i < 146 then
            if i < 141 then
              if i < 138 then
                if i < 137 then
                  (20011,181,0,0)
                else
                  (20043,182,0,0)
              else
                if i < 139 then
                  (20107,183,0,0)
                else
                  if i < 140 then
                    (20235,184,0,0)
                  else
                    (20299,185,0,0)
            else
              if i < 143 then
                if i < 142 then
                  (44548,186,187,0)
                else
                  (44572,188,0,0)
              else
                if i < 144 then
                  (44588,189,0,0)
                else
                  if i < 145 then
                    (44620,190,0,0)
                  else
                    (44684,191,0,0)
          else
            if i < 151 then
              if i < 148 then
                if i < 147 then
                  (44812,192,0,0)
                else
                  (40453,193,194,0)
              else
                if i < 149 then
                  (40477,195,0,0)
                else
                  if i < 150 then
                    (40493,196,0,0)
                  else
                    (40525,197,0,0)
            else
              if i < 153 then
                if i < 152 then
                  (40581,198,199,0)
                else
                  (40605,200,0,0)
              else
                if i < 154 then
                  (40621,201,0,0)
                else
                  if i < 155 then
                    (40653,202,0,0)
                  else
                    (40717,203,0,0)
  else
    if i < 234 then
      if i < 195 then
        if i < 175 then
          if i < 165 then
            if i < 160 then
              if i < 158 then
                if i < 157 then
                  (162310,204,205,0)
                else
                  (162334,206,0,0)
              else
                if i < 159 then
                  (162350,207,0,0)
                else
                  (162382,208,0,0)
            else
              if i < 162 then
                if i < 161 then
                  (162446,209,0,0)
                else
                  (162574,210,0,0)
              else
                if i < 163 then
                  (2223623,211,212,0)
                else
                  if i < 164 then
                    (2223647,213,0,0)
                  else
                    (2223663,214,0,0)
          else
            if i < 170 then
              if i < 167 then
                if i < 166 then
                  (2223695,215,0,0)
                else
                  (2223759,216,0,0)
              else
                if i < 168 then
                  (2223887,217,0,0)
                else
                  if i < 169 then
                    (5161,0,0,0)
                  else
                    (5193,0,0,0)
            else
              if i < 172 then
                if i < 171 then
                  (5257,0,0,0)
                else
                  (5385,0,0,0)
              else
                if i < 173 then
                  (5641,0,0,0)
                else
                  if i < 174 then
                    (11290,218,0,0)
                  else
                    (11306,219,0,0)
        else
          if i < 185 then
            if i < 180 then
              if i < 177 then
                if i < 176 then
                  (11338,220,0,0)
                else
                  (11402,221,0,0)
              else
                if i < 178 then
                  (11530,222,0,0)
                else
                  if i < 179 then
                    (39963,223,0,0)
                  else
                    (39979,224,0,0)
            else
              if i < 182 then
                if i < 181 then
                  (40011,225,0,0)
                else
                  (40075,226,0,0)
              else
                if i < 183 then
                  (40203,227,0,0)
                else
                  if i < 184 then
                    (40459,228,0,0)
                  else
                    (40587,229,0,0)
          else
            if i < 190 then
              if i < 187 then
                if i < 186 then
                  (89092,0,230,0)
                else
                  (89116,231,0,0)
              else
                if i < 188 then
                  (89132,232,0,0)
                else
                  if i < 189 then
                    (89164,233,0,0)
                  else
                    (89228,234,0,0)
            else
              if i < 192 then
                if i < 191 then
                  (89356,235,0,0)
                else
                  (89612,236,0,0)
              else
                if i < 193 then
                  (80901,0,237,0)
                else
                  if i < 194 then
                    (80925,238,0,0)
                  else
                    (80941,239,0,0)
      else
        if i < 214 then
          if i < 204 then
            if i < 199 then
              if i < 197 then
                if i < 196 then
                  (80973,240,0,0)
                else
                  (81037,241,0,0)
              else
                if i < 198 then
                  (81157,242,243,0)
                else
                  (81181,244,0,0)
            else
              if i < 201 then
                if i < 200 then
                  (81197,245,0,0)
                else
                  (81229,246,0,0)
              else
                if i < 202 then
                  (81293,247,0,0)
                else
                  if i < 203 then
                    (81421,248,0,0)
                  else
                    (324614,0,249,0)
          else
            if i < 209 then
              if i < 206 then
                if i < 205 then
                  (324638,250,0,0)
                else
                  (324654,251,0,0)
              else
                if i < 207 then
                  (324686,252,0,0)
                else
                  if i < 208 then
                    (324750,253,0,0)
                  else
                    (324878,254,0,0)
            else
              if i < 211 then
                if i < 210 then
                  (325134,255,0,0)
                else
                  (4447239,0,256,0)
              else
                if i < 212 then
                  (4447263,257,0,0)
                else
                  if i < 213 then
                    (4447279,258,0,0)
                  else
                    (4447311,259,0,0)
        else
          if i < 224 then
            if i < 219 then
              if i < 216 then
                if i < 215 then
                  (4447375,260,0,0)
                else
                  (4447503,261,0,0)
              else
                if i < 217 then
                  (4447759,262,0,0)
                else
                  if i < 218 then
                    (22570,0,0,0)
                  else
                    (22602,0,0,0)
            else
              if i < 221 then
                if i < 220 then
                  (22666,0,0,0)
                else
                  (22794,0,0,0)
              else
                if i < 222 then
                  (23050,0,0,0)
                else
                  if i < 223 then
                    (79915,0,0,0)
                  else
                    (79947,0,0,0)
          else
            if i < 229 then
              if i < 226 then
                if i < 225 then
                  (80011,0,0,0)
                else
                  (80139,0,0,0)
              else
                if i < 227 then
                  (80395,0,0,0)
                else
                  if i < 228 then
                    (80907,0,0,0)
                  else
                    (81163,263,0,0)
            else
              if i < 231 then
                if i < 230 then
                  (178204,264,0,0)
                else
                  (178220,265,0,0)
              else
                if i < 232 then
                  (178252,266,0,0)
                else
                  if i < 233 then
                    (178316,267,0,0)
                  else
                    (178444,268,0,0)
    else
      if i < 273 then
        if i < 253 then
          if i < 243 then
            if i < 238 then
              if i < 236 then
                if i < 235 then
                  (178700,269,0,0)
                else
                  (179212,270,0,0)
              else
                if i < 237 then
                  (161821,271,0,0)
                else
                  (161837,272,0,0)
            else
              if i < 240 then
                if i < 239 then
                  (161869,273,0,0)
                else
                  (161933,274,0,0)
              else
                if i < 241 then
                  (162061,275,0,0)
                else
                  if i < 242 then
                    (162309,276,277,0)
                  else
                    (162333,278,0,0)
          else
            if i < 248 then
              if i < 245 then
                if i < 244 then
                  (162349,279,0,0)
                else
                  (162381,280,0,0)
              else
                if i < 246 then
                  (162445,281,0,0)
                else
                  if i < 247 then
                    (162573,282,0,0)
                  else
                    (162829,283,0,0)
            else
              if i < 250 then
                if i < 249 then
                  (649246,284,0,0)
                else
                  (649262,285,0,0)
              else
                if i < 251 then
                  (649294,286,0,0)
                else
                  if i < 252 then
                    (649358,287,0,0)
                  else
                    (649486,288,0,0)
        else
          if i < 263 then
            if i < 258 then
              if i < 255 then
                if i < 254 then
                  (649742,289,0,0)
                else
                  (650254,290,0,0)
              else
                if i < 256 then
                  (8894495,291,0,0)
                else
                  if i < 257 then
                    (8894511,292,0,0)
                  else
                    (8894543,293,0,0)
            else
              if i < 260 then
                if i < 259 then
                  (8894607,294,0,0)
                else
                  (8894735,295,0,0)
              else
                if i < 261 then
                  (8894991,296,0,0)
                else
                  if i < 262 then
                    (8895503,297,0,0)
                  else
                    (162315,298,0,0)
          else
            if i < 268 then
              if i < 265 then
                if i < 264 then
                  (356396,0,0,0)
                else
                  (356428,0,0,0)
              else
                if i < 266 then
                  (356492,0,0,0)
                else
                  if i < 267 then
                    (356620,0,0,0)
                  else
                    (356876,0,0,0)
            else
              if i < 270 then
                if i < 269 then
                  (357388,0,0,0)
                else
                  (358412,0,0,0)
              else
                if i < 271 then
                  (323629,0,0,0)
                else
                  if i < 272 then
                    (323661,0,0,0)
                  else
                    (323725,0,0,0)
      else
        if i < 292 then
          if i < 282 then
            if i < 277 then
              if i < 275 then
                if i < 274 then
                  (323853,0,0,0)
                else
                  (324109,0,0,0)
              else
                if i < 276 then
                  (324613,0,299,0)
                else
                  (324637,300,0,0)
            else
              if i < 279 then
                if i < 278 then
                  (324653,301,0,0)
                else
                  (324685,302,0,0)
              else
                if i < 280 then
                  (324749,303,0,0)
                else
                  if i < 281 then
                    (324877,304,0,0)
                  else
                    (325133,305,0,0)
          else
            if i < 287 then
              if i < 284 then
                if i < 283 then
                  (325645,0,0,0)
                else
                  (1298478,0,0,0)
              else
                if i < 285 then
                  (1298510,0,0,0)
                else
                  if i < 286 then
                    (1298574,0,0,0)
                  else
                    (1298702,0,0,0)
            else
              if i < 289 then
                if i < 288 then
                  (1298958,0,0,0)
                else
                  (1299470,0,0,0)
              else
                if i < 290 then
                  (1300494,0,0,0)
                else
                  if i < 291 then
                    (17788975,0,0,0)
                  else
                    (17789007,0,0,0)
        else
          if i < 302 then
            if i < 297 then
              if i < 294 then
                if i < 293 then
                  (17789071,0,0,0)
                else
                  (17789199,0,0,0)
              else
                if i < 295 then
                  (17789455,0,0,0)
                else
                  if i < 296 then
                    (17789967,0,0,0)
                  else
                    (17790991,0,0,0)
            else
              if i < 299 then
                if i < 298 then
                  (324619,0,0,0)
                else
                  (649245,306,0,0)
              else
                if i < 300 then
                  (649261,307,0,0)
                else
                  if i < 301 then
                    (649293,308,0,0)
                  else
                    (649357,309,0,0)
          else
            if i < 307 then
              if i < 304 then
                if i < 303 then
                  (649485,310,0,0)
                else
                  (649741,311,0,0)
              else
                if i < 305 then
                  (650253,312,0,0)
                else
                  if i < 306 then
                    (1298477,0,0,0)
                  else
                    (1298509,0,0,0)
            else
              if i < 309 then
                if i < 308 then
                  (1298573,0,0,0)
                else
                  (1298701,0,0,0)
              else
                if i < 310 then
                  (1298957,0,0,0)
                else
                  if i < 311 then
                    (1299469,0,0,0)
                  else
                    (1300493,0,0,0)

def rows : Table := ⟨312,rowAt⟩

set_option maxHeartbeats 10000000 in
theorem rows_checked_0 : verifiedRange rows 0 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_32 : verifiedRange rows 32 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_64 : verifiedRange rows 64 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_96 : verifiedRange rows 96 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_128 : verifiedRange rows 128 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_160 : verifiedRange rows 160 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_192 : verifiedRange rows 192 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_224 : verifiedRange rows 224 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_256 : verifiedRange rows 256 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_288 : verifiedRange rows 288 24=true := by decide

theorem rows_verified : verified rows=true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hbound : i < 312 := List.mem_range.mp hi
  by_cases h160 : i < 160
  · by_cases h64 : i < 64
    · by_cases h32 : i < 32
      · exact verifiedRange_at rows 0 32 rows_checked_0 i (by omega) (by omega)
      · exact verifiedRange_at rows 32 32 rows_checked_32 i (by omega) (by omega)
    · by_cases h96 : i < 96
      · exact verifiedRange_at rows 64 32 rows_checked_64 i (by omega) (by omega)
      · by_cases h128 : i < 128
        · exact verifiedRange_at rows 96 32 rows_checked_96 i (by omega) (by omega)
        · exact verifiedRange_at rows 128 32 rows_checked_128 i (by omega) (by omega)
  · by_cases h224 : i < 224
    · by_cases h192 : i < 192
      · exact verifiedRange_at rows 160 32 rows_checked_160 i (by omega) (by omega)
      · exact verifiedRange_at rows 192 32 rows_checked_192 i (by omega) (by omega)
    · by_cases h256 : i < 256
      · exact verifiedRange_at rows 224 32 rows_checked_224 i (by omega) (by omega)
      · by_cases h288 : i < 288
        · exact verifiedRange_at rows 256 32 rows_checked_256 i (by omega) (by omega)
        · exact verifiedRange_at rows 288 24 rows_checked_288 i (by omega) (by omega)

theorem initial_member (w : List Bool) (hw : w ∈ endpointWords) : Member rows ⟨w,w,0⟩ := by
  simp only [endpointWords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst w; exact ⟨0, by decide, by decide⟩
  · subst w; exact ⟨1, by decide, by decide⟩
  · subst w; exact ⟨2, by decide, by decide⟩
  · subst w; exact ⟨3, by decide, by decide⟩
  · subst w; exact ⟨4, by decide, by decide⟩
  · subst w; exact ⟨5, by decide, by decide⟩
  · subst w; exact ⟨6, by decide, by decide⟩
  · subst w; exact ⟨7, by decide, by decide⟩

end Recaman.ThreeNonsuppliedQData
