/- Generated from q4-certificate.json; SHA256 6db508f2a4d841fb020215c18a5a9435c3296ebd464177e997c308a3c7cf0907 -/
import Recaman.FourNonsuppliedData

set_option maxRecDepth 100000

namespace Recaman.SixteenRootAreaData

open Recaman.LeadingRunSupply
open Recaman.ThreeNonsuppliedData (wordArea localSupply oldSignature decodeWord)
open Recaman.FourNonsuppliedData (endpointWords)

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
  ⟨endpointWords[code%16]!, decodeWord 22 (code/32), (code/16)%2⟩

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
  if i < 359 then
    if i < 179 then
      if i < 89 then
        if i < 44 then
          if i < 22 then
            if i < 11 then
              if i < 5 then
                if i < 2 then
                  if i < 1 then
                    (64,17,18,0)
                  else
                    (161,19,20,0)
                else
                  if i < 3 then
                    (354,21,0,0)
                  else
                    if i < 4 then
                      (1251,22,23,0)
                    else
                      (2788,24,25,0)
              else
                if i < 8 then
                  if i < 6 then
                    (2533,26,27,0)
                  else
                    if i < 7 then
                      (10150,28,29,0)
                    else
                      (138983,30,31,0)
                else
                  if i < 9 then
                    (5864,32,33,0)
                  else
                    if i < 10 then
                      (5609,34,35,0)
                    else
                      (22250,36,37,0)
            else
              if i < 16 then
                if i < 13 then
                  if i < 12 then
                    (5099,38,39,0)
                  else
                    (20332,40,0,0)
                else
                  if i < 14 then
                    (20205,41,42,0)
                  else
                    if i < 15 then
                      (73454,43,44,0)
                    else
                      (277999,45,46,0)
              else
                if i < 19 then
                  if i < 17 then
                    (128,47,48,0)
                  else
                    if i < 18 then
                      (176,49,0,0)
                    else
                      (321,50,51,0)
                else
                  if i < 20 then
                    (369,52,0,0)
                  else
                    if i < 21 then
                      (706,53,54,0)
                    else
                      (2499,55,56,0)
          else
            if i < 33 then
              if i < 27 then
                if i < 24 then
                  if i < 23 then
                    (2547,57,0,0)
                  else
                    (5572,58,59,0)
                else
                  if i < 25 then
                    (5620,60,0,0)
                  else
                    if i < 26 then
                      (5061,61,0,62)
                    else
                      (5109,63,0,0)
              else
                if i < 30 then
                  if i < 28 then
                    (20294,64,65,0)
                  else
                    if i < 29 then
                      (20342,66,0,0)
                    else
                      (277959,67,68,0)
                else
                  if i < 31 then
                    (278007,69,0,0)
                  else
                    if i < 32 then
                      (11720,70,71,0)
                    else
                      (11768,72,0,0)
            else
              if i < 38 then
                if i < 35 then
                  if i < 34 then
                    (11209,73,74,0)
                  else
                    (11257,75,0,0)
                else
                  if i < 36 then
                    (44490,76,77,0)
                  else
                    if i < 37 then
                      (44538,78,0,0)
                    else
                      (10187,79,80,0)
              else
                if i < 41 then
                  if i < 39 then
                    (10235,81,0,0)
                  else
                    if i < 40 then
                      (40652,82,83,0)
                    else
                      (40397,84,85,0)
                else
                  if i < 42 then
                    (40445,86,0,0)
                  else
                    if i < 43 then
                      (146894,87,88,0)
                    else
                      (146942,89,0,0)
        else
          if i < 66 then
            if i < 55 then
              if i < 49 then
                if i < 46 then
                  if i < 45 then
                    (555983,90,91,0)
                  else
                    (556031,92,0,0)
                else
                  if i < 47 then
                    (256,93,94,0)
                  else
                    if i < 48 then
                      (304,95,0,0)
                    else
                      (336,96,0,0)
              else
                if i < 52 then
                  if i < 50 then
                    (641,97,98,0)
                  else
                    if i < 51 then
                      (689,99,0,0)
                    else
                      (721,100,0,0)
                else
                  if i < 53 then
                    (1410,101,102,0)
                  else
                    if i < 54 then
                      (1458,103,0,0)
                    else
                      (4995,104,105,0)
            else
              if i < 60 then
                if i < 57 then
                  if i < 56 then
                    (5043,106,0,0)
                  else
                    (5075,107,0,108)
                else
                  if i < 58 then
                    (11140,109,110,0)
                  else
                    if i < 59 then
                      (11188,111,0,0)
                    else
                      (11220,112,0,0)
              else
                if i < 63 then
                  if i < 61 then
                    (10117,113,114,0)
                  else
                    if i < 62 then
                      (10149,115,116,0)
                    else
                      (10197,117,0,0)
                else
                  if i < 64 then
                    (40582,118,119,0)
                  else
                    if i < 65 then
                      (40630,120,0,0)
                    else
                      (40662,121,0,0)
          else
            if i < 77 then
              if i < 71 then
                if i < 68 then
                  if i < 67 then
                    (555911,122,123,0)
                  else
                    (555959,124,0,0)
                else
                  if i < 69 then
                    (555991,125,0,0)
                  else
                    if i < 70 then
                      (23432,126,127,0)
                    else
                      (23480,128,0,0)
              else
                if i < 74 then
                  if i < 72 then
                    (23512,129,0,0)
                  else
                    if i < 73 then
                      (22409,130,131,0)
                    else
                      (22457,132,0,0)
                else
                  if i < 75 then
                    (22489,133,0,0)
                  else
                    if i < 76 then
                      (88970,134,135,0)
                    else
                      (89018,136,0,0)
            else
              if i < 83 then
                if i < 80 then
                  if i < 78 then
                    (89050,137,0,0)
                  else
                    if i < 79 then
                      (20363,138,139,0)
                    else
                      (20411,140,0,0)
                else
                  if i < 81 then
                    (20443,141,0,0)
                  else
                    if i < 82 then
                      (81292,142,143,0)
                    else
                      (81340,144,0,0)
              else
                if i < 86 then
                  if i < 84 then
                    (80781,145,146,0)
                  else
                    if i < 85 then
                      (80829,147,0,0)
                    else
                      (80861,148,0,0)
                else
                  if i < 87 then
                    (293774,149,150,0)
                  else
                    if i < 88 then
                      (293822,151,0,0)
                    else
                      (293854,152,0,0)
      else
        if i < 134 then
          if i < 111 then
            if i < 100 then
              if i < 94 then
                if i < 91 then
                  if i < 90 then
                    (1111951,153,154,0)
                  else
                    (1111999,155,0,0)
                else
                  if i < 92 then
                    (1112031,156,0,0)
                  else
                    if i < 93 then
                      (512,0,157,0)
                    else
                      (560,158,0,0)
              else
                if i < 97 then
                  if i < 95 then
                    (592,159,0,0)
                  else
                    if i < 96 then
                      (656,160,0,0)
                    else
                      (1281,161,162,0)
                else
                  if i < 98 then
                    (1329,163,0,0)
                  else
                    if i < 99 then
                      (1361,164,0,0)
                    else
                      (1425,165,0,0)
            else
              if i < 105 then
                if i < 102 then
                  if i < 101 then
                    (2818,166,167,0)
                  else
                    (2866,168,0,0)
                else
                  if i < 103 then
                    (2898,169,0,0)
                  else
                    if i < 104 then
                      (9987,170,171,0)
                    else
                      (10035,172,0,0)
              else
                if i < 108 then
                  if i < 106 then
                    (10067,173,0,0)
                  else
                    if i < 107 then
                      (10131,174,0,0)
                    else
                      (10163,175,0,0)
                else
                  if i < 109 then
                    (22276,176,177,0)
                  else
                    if i < 110 then
                      (22324,178,0,0)
                    else
                      (22356,179,0,0)
          else
            if i < 122 then
              if i < 116 then
                if i < 113 then
                  if i < 112 then
                    (22420,180,0,0)
                  else
                    (20229,181,182,0)
                else
                  if i < 114 then
                    (20277,183,0,0)
                  else
                    if i < 115 then
                      (20293,184,185,0)
                    else
                      (20341,186,0,0)
              else
                if i < 119 then
                  if i < 117 then
                    (20373,187,0,0)
                  else
                    if i < 118 then
                      (81158,188,189,0)
                    else
                      (81206,190,0,0)
                else
                  if i < 120 then
                    (81238,191,0,0)
                  else
                    if i < 121 then
                      (81302,192,0,0)
                    else
                      (1111815,193,194,0)
            else
              if i < 128 then
                if i < 125 then
                  if i < 123 then
                    (1111863,195,0,0)
                  else
                    if i < 124 then
                      (1111895,196,0,0)
                    else
                      (1111959,197,0,0)
                else
                  if i < 126 then
                    (46856,198,199,0)
                  else
                    if i < 127 then
                      (46904,200,0,0)
                    else
                      (46936,201,0,0)
              else
                if i < 131 then
                  if i < 129 then
                    (47000,202,0,0)
                  else
                    if i < 130 then
                      (44809,203,204,0)
                    else
                      (44857,205,0,0)
                else
                  if i < 132 then
                    (44889,206,0,0)
                  else
                    if i < 133 then
                      (44953,207,0,0)
                    else
                      (177930,208,209,0)
        else
          if i < 156 then
            if i < 145 then
              if i < 139 then
                if i < 136 then
                  if i < 135 then
                    (177978,210,0,0)
                  else
                    (178010,211,0,0)
                else
                  if i < 137 then
                    (178074,212,0,0)
                  else
                    if i < 138 then
                      (40715,213,214,0)
                    else
                      (40763,215,0,0)
              else
                if i < 142 then
                  if i < 140 then
                    (40795,216,0,0)
                  else
                    if i < 141 then
                      (40859,217,0,0)
                    else
                      (162572,218,219,0)
                else
                  if i < 143 then
                    (162620,220,0,0)
                  else
                    if i < 144 then
                      (162652,221,0,0)
                    else
                      (161549,222,223,0)
            else
              if i < 150 then
                if i < 147 then
                  if i < 146 then
                    (161597,224,0,0)
                  else
                    (161629,225,0,0)
                else
                  if i < 148 then
                    (161693,226,0,0)
                  else
                    if i < 149 then
                      (587534,227,228,0)
                    else
                      (587582,229,0,0)
              else
                if i < 153 then
                  if i < 151 then
                    (587614,230,0,0)
                  else
                    if i < 152 then
                      (587678,231,0,0)
                    else
                      (2223887,232,233,0)
                else
                  if i < 154 then
                    (2223935,234,0,0)
                  else
                    if i < 155 then
                      (2223967,235,0,0)
                    else
                      (2224031,236,0,0)
          else
            if i < 167 then
              if i < 161 then
                if i < 158 then
                  if i < 157 then
                    (1072,237,0,0)
                  else
                    (1104,238,0,0)
                else
                  if i < 159 then
                    (1168,239,0,0)
                  else
                    if i < 160 then
                      (1296,240,0,0)
                    else
                      (2561,0,241,0)
              else
                if i < 164 then
                  if i < 162 then
                    (2609,242,0,0)
                  else
                    if i < 163 then
                      (2641,243,0,0)
                    else
                      (2705,244,0,0)
                else
                  if i < 165 then
                    (2833,245,0,0)
                  else
                    if i < 166 then
                      (5634,246,247,0)
                    else
                      (5682,248,0,0)
            else
              if i < 173 then
                if i < 170 then
                  if i < 168 then
                    (5714,249,0,0)
                  else
                    if i < 169 then
                      (5778,250,0,0)
                    else
                      (19971,251,252,0)
                else
                  if i < 171 then
                    (20019,253,0,0)
                  else
                    if i < 172 then
                      (20051,254,0,0)
                    else
                      (20115,255,0,0)
              else
                if i < 176 then
                  if i < 174 then
                    (20243,256,0,0)
                  else
                    if i < 175 then
                      (20307,257,0,0)
                    else
                      (44548,258,259,0)
                else
                  if i < 177 then
                    (44596,260,0,0)
                  else
                    if i < 178 then
                      (44628,261,0,0)
                    else
                      (44692,262,0,0)
    else
      if i < 269 then
        if i < 224 then
          if i < 201 then
            if i < 190 then
              if i < 184 then
                if i < 181 then
                  if i < 180 then
                    (44820,263,0,0)
                  else
                    (40453,264,265,0)
                else
                  if i < 182 then
                    (40501,266,0,0)
                  else
                    if i < 183 then
                      (40533,267,0,0)
                    else
                      (40581,268,269,0)
              else
                if i < 187 then
                  if i < 185 then
                    (40629,270,0,0)
                  else
                    if i < 186 then
                      (40661,271,0,0)
                    else
                      (40725,272,0,0)
                else
                  if i < 188 then
                    (162310,273,274,0)
                  else
                    if i < 189 then
                      (162358,275,0,0)
                    else
                      (162390,276,0,0)
            else
              if i < 195 then
                if i < 192 then
                  if i < 191 then
                    (162454,277,0,0)
                  else
                    (162582,278,0,0)
                else
                  if i < 193 then
                    (2223623,279,280,0)
                  else
                    if i < 194 then
                      (2223671,281,0,0)
                    else
                      (2223703,282,0,0)
              else
                if i < 198 then
                  if i < 196 then
                    (2223767,283,0,0)
                  else
                    if i < 197 then
                      (2223895,284,0,0)
                    else
                      (93704,285,286,0)
                else
                  if i < 199 then
                    (93752,287,0,0)
                  else
                    if i < 200 then
                      (93784,288,0,0)
                    else
                      (93848,289,0,0)
          else
            if i < 212 then
              if i < 206 then
                if i < 203 then
                  if i < 202 then
                    (93976,290,0,0)
                  else
                    (89609,291,292,0)
                else
                  if i < 204 then
                    (89657,293,0,0)
                  else
                    if i < 205 then
                      (89689,294,0,0)
                    else
                      (89753,295,0,0)
              else
                if i < 209 then
                  if i < 207 then
                    (89881,296,0,0)
                  else
                    if i < 208 then
                      (355850,297,298,0)
                    else
                      (355898,299,0,0)
                else
                  if i < 210 then
                    (355930,300,0,0)
                  else
                    if i < 211 then
                      (355994,301,0,0)
                    else
                      (356122,302,0,0)
            else
              if i < 218 then
                if i < 215 then
                  if i < 213 then
                    (81419,303,304,0)
                  else
                    if i < 214 then
                      (81467,305,0,0)
                    else
                      (81499,306,0,0)
                else
                  if i < 216 then
                    (81563,307,0,0)
                  else
                    if i < 217 then
                      (81691,308,0,0)
                    else
                      (325132,309,310,0)
              else
                if i < 221 then
                  if i < 219 then
                    (325180,311,0,0)
                  else
                    if i < 220 then
                      (325212,312,0,0)
                    else
                      (325276,313,0,0)
                else
                  if i < 222 then
                    (323085,314,315,0)
                  else
                    if i < 223 then
                      (323133,316,0,0)
                    else
                      (323165,317,0,0)
        else
          if i < 246 then
            if i < 235 then
              if i < 229 then
                if i < 226 then
                  if i < 225 then
                    (323229,318,0,0)
                  else
                    (323357,319,0,0)
                else
                  if i < 227 then
                    (1175054,320,321,0)
                  else
                    if i < 228 then
                      (1175102,322,0,0)
                    else
                      (1175134,323,0,0)
              else
                if i < 232 then
                  if i < 230 then
                    (1175198,324,0,0)
                  else
                    if i < 231 then
                      (1175326,325,0,0)
                    else
                      (4447759,326,327,0)
                else
                  if i < 233 then
                    (4447807,328,0,0)
                  else
                    if i < 234 then
                      (4447839,329,0,0)
                    else
                      (4447903,330,0,0)
            else
              if i < 240 then
                if i < 237 then
                  if i < 236 then
                    (4448031,331,0,0)
                  else
                    (2128,0,0,0)
                else
                  if i < 238 then
                    (2192,0,0,0)
                  else
                    if i < 239 then
                      (2320,0,0,0)
                    else
                      (2576,0,0,0)
              else
                if i < 243 then
                  if i < 241 then
                    (5169,332,0,0)
                  else
                    if i < 242 then
                      (5201,333,0,0)
                    else
                      (5265,334,0,0)
                else
                  if i < 244 then
                    (5393,335,0,0)
                  else
                    if i < 245 then
                      (5649,336,0,0)
                    else
                      (11266,0,337,0)
          else
            if i < 257 then
              if i < 251 then
                if i < 248 then
                  if i < 247 then
                    (11314,338,0,0)
                  else
                    (11346,339,0,0)
                else
                  if i < 249 then
                    (11410,340,0,0)
                  else
                    if i < 250 then
                      (11538,341,0,0)
                    else
                      (39939,0,342,0)
              else
                if i < 254 then
                  if i < 252 then
                    (39987,343,0,0)
                  else
                    if i < 253 then
                      (40019,344,0,0)
                    else
                      (40083,345,0,0)
                else
                  if i < 255 then
                    (40211,346,0,0)
                  else
                    if i < 256 then
                      (40467,347,0,0)
                    else
                      (40595,348,0,0)
            else
              if i < 263 then
                if i < 260 then
                  if i < 258 then
                    (89092,349,350,0)
                  else
                    if i < 259 then
                      (89140,351,0,0)
                    else
                      (89172,352,0,0)
                else
                  if i < 261 then
                    (89236,353,0,0)
                  else
                    if i < 262 then
                      (89364,354,0,0)
                    else
                      (89620,355,0,0)
              else
                if i < 266 then
                  if i < 264 then
                    (80901,356,357,0)
                  else
                    if i < 265 then
                      (80949,358,0,0)
                    else
                      (80981,359,0,0)
                else
                  if i < 267 then
                    (81045,360,0,0)
                  else
                    if i < 268 then
                      (81157,361,362,0)
                    else
                      (81205,363,0,0)
      else
        if i < 314 then
          if i < 291 then
            if i < 280 then
              if i < 274 then
                if i < 271 then
                  if i < 270 then
                    (81237,364,0,0)
                  else
                    (81301,365,0,0)
                else
                  if i < 272 then
                    (81429,366,0,0)
                  else
                    if i < 273 then
                      (324614,367,368,0)
                    else
                      (324662,369,0,0)
              else
                if i < 277 then
                  if i < 275 then
                    (324694,370,0,0)
                  else
                    if i < 276 then
                      (324758,371,0,0)
                    else
                      (324886,372,0,0)
                else
                  if i < 278 then
                    (325142,373,0,0)
                  else
                    if i < 279 then
                      (4447239,374,375,0)
                    else
                      (4447287,376,0,0)
            else
              if i < 285 then
                if i < 282 then
                  if i < 281 then
                    (4447319,377,0,0)
                  else
                    (4447383,378,0,0)
                else
                  if i < 283 then
                    (4447511,379,0,0)
                  else
                    if i < 284 then
                      (4447767,380,0,0)
                    else
                      (187400,381,382,0)
              else
                if i < 288 then
                  if i < 286 then
                    (187448,383,0,0)
                  else
                    if i < 287 then
                      (187480,384,0,0)
                    else
                      (187544,385,0,0)
                else
                  if i < 289 then
                    (187672,386,0,0)
                  else
                    if i < 290 then
                      (187928,387,0,0)
                    else
                      (179209,388,389,0)
          else
            if i < 302 then
              if i < 296 then
                if i < 293 then
                  if i < 292 then
                    (179257,390,0,0)
                  else
                    (179289,391,0,0)
                else
                  if i < 294 then
                    (179353,392,0,0)
                  else
                    if i < 295 then
                      (179481,393,0,0)
                    else
                      (179737,394,0,0)
              else
                if i < 299 then
                  if i < 297 then
                    (711690,395,396,0)
                  else
                    if i < 298 then
                      (711738,397,0,0)
                    else
                      (711770,398,0,0)
                else
                  if i < 300 then
                    (711834,399,0,0)
                  else
                    if i < 301 then
                      (711962,400,0,0)
                    else
                      (712218,401,0,0)
            else
              if i < 308 then
                if i < 305 then
                  if i < 303 then
                    (162827,402,403,0)
                  else
                    if i < 304 then
                      (162875,404,0,0)
                    else
                      (162907,405,0,0)
                else
                  if i < 306 then
                    (162971,406,0,0)
                  else
                    if i < 307 then
                      (163099,407,0,0)
                    else
                      (163355,408,0,0)
              else
                if i < 311 then
                  if i < 309 then
                    (650252,409,410,0)
                  else
                    if i < 310 then
                      (650300,411,0,0)
                    else
                      (650332,412,0,0)
                else
                  if i < 312 then
                    (650396,413,0,0)
                  else
                    if i < 313 then
                      (650524,414,0,0)
                    else
                      (646157,415,416,0)
        else
          if i < 336 then
            if i < 325 then
              if i < 319 then
                if i < 316 then
                  if i < 315 then
                    (646205,417,0,0)
                  else
                    (646237,418,0,0)
                else
                  if i < 317 then
                    (646301,419,0,0)
                  else
                    if i < 318 then
                      (646429,420,0,0)
                    else
                      (646685,421,0,0)
              else
                if i < 322 then
                  if i < 320 then
                    (2350094,422,423,0)
                  else
                    if i < 321 then
                      (2350142,424,0,0)
                    else
                      (2350174,425,0,0)
                else
                  if i < 323 then
                    (2350238,426,0,0)
                  else
                    if i < 324 then
                      (2350366,427,0,0)
                    else
                      (2350622,428,0,0)
            else
              if i < 330 then
                if i < 327 then
                  if i < 326 then
                    (8895503,429,430,0)
                  else
                    (8895551,431,0,0)
                else
                  if i < 328 then
                    (8895583,432,0,0)
                  else
                    if i < 329 then
                      (8895647,433,0,0)
                    else
                      (8895775,434,0,0)
              else
                if i < 333 then
                  if i < 331 then
                    (8896031,435,0,0)
                  else
                    if i < 332 then
                      (10321,0,0,0)
                    else
                      (10385,0,0,0)
                else
                  if i < 334 then
                    (10513,0,0,0)
                  else
                    if i < 335 then
                      (10769,0,0,0)
                    else
                      (11281,0,0,0)
          else
            if i < 347 then
              if i < 341 then
                if i < 338 then
                  if i < 337 then
                    (22578,436,0,0)
                  else
                    (22610,437,0,0)
                else
                  if i < 339 then
                    (22674,438,0,0)
                  else
                    if i < 340 then
                      (22802,439,0,0)
                    else
                      (23058,440,0,0)
              else
                if i < 344 then
                  if i < 342 then
                    (79923,441,0,0)
                  else
                    if i < 343 then
                      (79955,442,0,0)
                    else
                      (80019,443,0,0)
                else
                  if i < 345 then
                    (80147,444,0,0)
                  else
                    if i < 346 then
                      (80403,445,0,0)
                    else
                      (80915,446,0,0)
            else
              if i < 353 then
                if i < 350 then
                  if i < 348 then
                    (81171,447,0,0)
                  else
                    if i < 349 then
                      (178180,0,448,0)
                    else
                      (178228,449,0,0)
                else
                  if i < 351 then
                    (178260,450,0,0)
                  else
                    if i < 352 then
                      (178324,451,0,0)
                    else
                      (178452,452,0,0)
              else
                if i < 356 then
                  if i < 354 then
                    (178708,453,0,0)
                  else
                    if i < 355 then
                      (179220,454,0,0)
                    else
                      (161797,0,455,0)
                else
                  if i < 357 then
                    (161845,456,0,0)
                  else
                    if i < 358 then
                      (161877,457,0,0)
                    else
                      (161941,458,0,0)
  else
    if i < 539 then
      if i < 449 then
        if i < 404 then
          if i < 381 then
            if i < 370 then
              if i < 364 then
                if i < 361 then
                  if i < 360 then
                    (162069,459,0,0)
                  else
                    (162309,460,461,0)
                else
                  if i < 362 then
                    (162357,462,0,0)
                  else
                    if i < 363 then
                      (162389,463,0,0)
                    else
                      (162453,464,0,0)
              else
                if i < 367 then
                  if i < 365 then
                    (162581,465,0,0)
                  else
                    if i < 366 then
                      (162837,466,0,0)
                    else
                      (649222,0,467,0)
                else
                  if i < 368 then
                    (649270,468,0,0)
                  else
                    if i < 369 then
                      (649302,469,0,0)
                    else
                      (649366,470,0,0)
            else
              if i < 375 then
                if i < 372 then
                  if i < 371 then
                    (649494,471,0,0)
                  else
                    (649750,472,0,0)
                else
                  if i < 373 then
                    (650262,473,0,0)
                  else
                    if i < 374 then
                      (8894471,0,474,0)
                    else
                      (8894519,475,0,0)
              else
                if i < 378 then
                  if i < 376 then
                    (8894551,476,0,0)
                  else
                    if i < 377 then
                      (8894615,477,0,0)
                    else
                      (8894743,478,0,0)
                else
                  if i < 379 then
                    (8894999,479,0,0)
                  else
                    if i < 380 then
                      (8895511,480,0,0)
                    else
                      (374792,481,482,0)
          else
            if i < 392 then
              if i < 386 then
                if i < 383 then
                  if i < 382 then
                    (374840,483,0,0)
                  else
                    (374872,484,0,0)
                else
                  if i < 384 then
                    (374936,485,0,0)
                  else
                    if i < 385 then
                      (375064,486,0,0)
                    else
                      (375320,487,0,0)
              else
                if i < 389 then
                  if i < 387 then
                    (375832,488,0,0)
                  else
                    if i < 388 then
                      (358409,489,490,0)
                    else
                      (358457,491,0,0)
                else
                  if i < 390 then
                    (358489,492,0,0)
                  else
                    if i < 391 then
                      (358553,493,0,0)
                    else
                      (358681,494,0,0)
            else
              if i < 398 then
                if i < 395 then
                  if i < 393 then
                    (358937,495,0,0)
                  else
                    if i < 394 then
                      (359449,496,0,0)
                    else
                      (1423370,497,498,0)
                else
                  if i < 396 then
                    (1423418,499,0,0)
                  else
                    if i < 397 then
                      (1423450,500,0,0)
                    else
                      (1423514,501,0,0)
              else
                if i < 401 then
                  if i < 399 then
                    (1423642,502,0,0)
                  else
                    if i < 400 then
                      (1423898,503,0,0)
                    else
                      (1424410,504,0,0)
                else
                  if i < 402 then
                    (325643,505,506,0)
                  else
                    if i < 403 then
                      (325691,507,0,0)
                    else
                      (325723,508,0,0)
        else
          if i < 426 then
            if i < 415 then
              if i < 409 then
                if i < 406 then
                  if i < 405 then
                    (325787,509,0,0)
                  else
                    (325915,510,0,0)
                else
                  if i < 407 then
                    (326171,511,0,0)
                  else
                    if i < 408 then
                      (326683,512,0,0)
                    else
                      (1300492,513,514,0)
              else
                if i < 412 then
                  if i < 410 then
                    (1300540,515,0,0)
                  else
                    if i < 411 then
                      (1300572,516,0,0)
                    else
                      (1300636,517,0,0)
                else
                  if i < 413 then
                    (1300764,518,0,0)
                  else
                    if i < 414 then
                      (1301020,519,0,0)
                    else
                      (1292301,520,521,0)
            else
              if i < 420 then
                if i < 417 then
                  if i < 416 then
                    (1292349,522,0,0)
                  else
                    (1292381,523,0,0)
                else
                  if i < 418 then
                    (1292445,524,0,0)
                  else
                    if i < 419 then
                      (1292573,525,0,0)
                    else
                      (1292829,526,0,0)
              else
                if i < 423 then
                  if i < 421 then
                    (1293341,527,0,0)
                  else
                    if i < 422 then
                      (4700174,528,529,0)
                    else
                      (4700222,530,0,0)
                else
                  if i < 424 then
                    (4700254,531,0,0)
                  else
                    if i < 425 then
                      (4700318,532,0,0)
                    else
                      (4700446,533,0,0)
          else
            if i < 437 then
              if i < 431 then
                if i < 428 then
                  if i < 427 then
                    (4700702,534,0,0)
                  else
                    (4701214,535,0,0)
                else
                  if i < 429 then
                    (17790991,536,537,0)
                  else
                    if i < 430 then
                      (17791039,538,0,0)
                    else
                      (17791071,539,0,0)
              else
                if i < 434 then
                  if i < 432 then
                    (17791135,540,0,0)
                  else
                    if i < 433 then
                      (17791263,541,0,0)
                    else
                      (17791519,542,0,0)
                else
                  if i < 435 then
                    (17792031,543,0,0)
                  else
                    if i < 436 then
                      (45138,0,0,0)
                    else
                      (45202,0,0,0)
            else
              if i < 443 then
                if i < 440 then
                  if i < 438 then
                    (45330,0,0,0)
                  else
                    if i < 439 then
                      (45586,0,0,0)
                    else
                      (46098,0,0,0)
                else
                  if i < 441 then
                    (159827,0,0,0)
                  else
                    if i < 442 then
                      (159891,0,0,0)
                    else
                      (160019,0,0,0)
              else
                if i < 446 then
                  if i < 444 then
                    (160275,0,0,0)
                  else
                    if i < 445 then
                      (160787,0,0,0)
                    else
                      (161811,0,0,0)
                else
                  if i < 447 then
                    (162323,544,0,0)
                  else
                    if i < 448 then
                      (356404,545,0,0)
                    else
                      (356436,546,0,0)
      else
        if i < 494 then
          if i < 471 then
            if i < 460 then
              if i < 454 then
                if i < 451 then
                  if i < 450 then
                    (356500,547,0,0)
                  else
                    (356628,548,0,0)
                else
                  if i < 452 then
                    (356884,549,0,0)
                  else
                    if i < 453 then
                      (357396,550,0,0)
                    else
                      (358420,551,0,0)
              else
                if i < 457 then
                  if i < 455 then
                    (323637,552,0,0)
                  else
                    if i < 456 then
                      (323669,553,0,0)
                    else
                      (323733,554,0,0)
                else
                  if i < 458 then
                    (323861,555,0,0)
                  else
                    if i < 459 then
                      (324117,556,0,0)
                    else
                      (324613,557,558,0)
            else
              if i < 465 then
                if i < 462 then
                  if i < 461 then
                    (324661,559,0,0)
                  else
                    (324693,560,0,0)
                else
                  if i < 463 then
                    (324757,561,0,0)
                  else
                    if i < 464 then
                      (324885,562,0,0)
                    else
                      (325141,563,0,0)
              else
                if i < 468 then
                  if i < 466 then
                    (325653,564,0,0)
                  else
                    if i < 467 then
                      (1298486,565,0,0)
                    else
                      (1298518,566,0,0)
                else
                  if i < 469 then
                    (1298582,567,0,0)
                  else
                    if i < 470 then
                      (1298710,568,0,0)
                    else
                      (1298966,569,0,0)
          else
            if i < 482 then
              if i < 476 then
                if i < 473 then
                  if i < 472 then
                    (1299478,570,0,0)
                  else
                    (1300502,571,0,0)
                else
                  if i < 474 then
                    (17788983,572,0,0)
                  else
                    if i < 475 then
                      (17789015,573,0,0)
                    else
                      (17789079,574,0,0)
              else
                if i < 479 then
                  if i < 477 then
                    (17789207,575,0,0)
                  else
                    if i < 478 then
                      (17789463,576,0,0)
                    else
                      (17789975,577,0,0)
                else
                  if i < 480 then
                    (17790999,578,0,0)
                  else
                    if i < 481 then
                      (749576,0,579,0)
                    else
                      (749624,580,0,0)
            else
              if i < 488 then
                if i < 485 then
                  if i < 483 then
                    (749656,581,0,0)
                  else
                    if i < 484 then
                      (749720,582,0,0)
                    else
                      (749848,583,0,0)
                else
                  if i < 486 then
                    (750104,584,0,0)
                  else
                    if i < 487 then
                      (750616,585,0,0)
                    else
                      (751640,586,0,0)
              else
                if i < 491 then
                  if i < 489 then
                    (716809,0,587,0)
                  else
                    if i < 490 then
                      (716857,588,0,0)
                    else
                      (716889,589,0,0)
                else
                  if i < 492 then
                    (716953,590,0,0)
                  else
                    if i < 493 then
                      (717081,591,0,0)
                    else
                      (717337,592,0,0)
        else
          if i < 516 then
            if i < 505 then
              if i < 499 then
                if i < 496 then
                  if i < 495 then
                    (717849,593,0,0)
                  else
                    (718873,594,0,0)
                else
                  if i < 497 then
                    (2846730,0,595,0)
                  else
                    if i < 498 then
                      (2846778,596,0,0)
                    else
                      (2846810,597,0,0)
              else
                if i < 502 then
                  if i < 500 then
                    (2846874,598,0,0)
                  else
                    if i < 501 then
                      (2847002,599,0,0)
                    else
                      (2847258,600,0,0)
                else
                  if i < 503 then
                    (2847770,601,0,0)
                  else
                    if i < 504 then
                      (2848794,602,0,0)
                    else
                      (651275,0,603,0)
            else
              if i < 510 then
                if i < 507 then
                  if i < 506 then
                    (651323,604,0,0)
                  else
                    (651355,605,0,0)
                else
                  if i < 508 then
                    (651419,606,0,0)
                  else
                    if i < 509 then
                      (651547,607,0,0)
                    else
                      (651803,608,0,0)
              else
                if i < 513 then
                  if i < 511 then
                    (652315,609,0,0)
                  else
                    if i < 512 then
                      (653339,610,0,0)
                    else
                      (2600972,0,611,0)
                else
                  if i < 514 then
                    (2601020,612,0,0)
                  else
                    if i < 515 then
                      (2601052,613,0,0)
                    else
                      (2601116,614,0,0)
          else
            if i < 527 then
              if i < 521 then
                if i < 518 then
                  if i < 517 then
                    (2601244,615,0,0)
                  else
                    (2601500,616,0,0)
                else
                  if i < 519 then
                    (2602012,617,0,0)
                  else
                    if i < 520 then
                      (2584589,0,618,0)
                    else
                      (2584637,619,0,0)
              else
                if i < 524 then
                  if i < 522 then
                    (2584669,620,0,0)
                  else
                    if i < 523 then
                      (2584733,621,0,0)
                    else
                      (2584861,622,0,0)
                else
                  if i < 525 then
                    (2585117,623,0,0)
                  else
                    if i < 526 then
                      (2585629,624,0,0)
                    else
                      (2586653,625,0,0)
            else
              if i < 533 then
                if i < 530 then
                  if i < 528 then
                    (9400334,0,626,0)
                  else
                    if i < 529 then
                      (9400382,627,0,0)
                    else
                      (9400414,628,0,0)
                else
                  if i < 531 then
                    (9400478,629,0,0)
                  else
                    if i < 532 then
                      (9400606,630,0,0)
                    else
                      (9400862,631,0,0)
              else
                if i < 536 then
                  if i < 534 then
                    (9401374,632,0,0)
                  else
                    if i < 535 then
                      (9402398,633,0,0)
                    else
                      (35581967,0,634,0)
                else
                  if i < 537 then
                    (35582015,635,0,0)
                  else
                    if i < 538 then
                      (35582047,636,0,0)
                    else
                      (35582111,637,0,0)
    else
      if i < 629 then
        if i < 584 then
          if i < 561 then
            if i < 550 then
              if i < 544 then
                if i < 541 then
                  if i < 540 then
                    (35582239,638,0,0)
                  else
                    (35582495,639,0,0)
                else
                  if i < 542 then
                    (35583007,640,0,0)
                  else
                    if i < 543 then
                      (35584031,641,0,0)
                    else
                      (324627,642,0,0)
              else
                if i < 547 then
                  if i < 545 then
                    (712788,0,0,0)
                  else
                    if i < 546 then
                      (712852,0,0,0)
                    else
                      (712980,0,0,0)
                else
                  if i < 548 then
                    (713236,0,0,0)
                  else
                    if i < 549 then
                      (713748,0,0,0)
                    else
                      (714772,0,0,0)
            else
              if i < 555 then
                if i < 552 then
                  if i < 551 then
                    (716820,0,0,0)
                  else
                    (647253,0,0,0)
                else
                  if i < 553 then
                    (647317,0,0,0)
                  else
                    if i < 554 then
                      (647445,0,0,0)
                    else
                      (647701,0,0,0)
              else
                if i < 558 then
                  if i < 556 then
                    (648213,0,0,0)
                  else
                    if i < 557 then
                      (649221,0,643,0)
                    else
                      (649269,644,0,0)
                else
                  if i < 559 then
                    (649301,645,0,0)
                  else
                    if i < 560 then
                      (649365,646,0,0)
                    else
                      (649493,647,0,0)
          else
            if i < 572 then
              if i < 566 then
                if i < 563 then
                  if i < 562 then
                    (649749,648,0,0)
                  else
                    (650261,649,0,0)
                else
                  if i < 564 then
                    (651285,0,0,0)
                  else
                    if i < 565 then
                      (2596950,0,0,0)
                    else
                      (2597014,0,0,0)
              else
                if i < 569 then
                  if i < 567 then
                    (2597142,0,0,0)
                  else
                    if i < 568 then
                      (2597398,0,0,0)
                    else
                      (2597910,0,0,0)
                else
                  if i < 570 then
                    (2598934,0,0,0)
                  else
                    if i < 571 then
                      (2600982,0,0,0)
                    else
                      (35577943,0,0,0)
            else
              if i < 578 then
                if i < 575 then
                  if i < 573 then
                    (35578007,0,0,0)
                  else
                    if i < 574 then
                      (35578135,0,0,0)
                    else
                      (35578391,0,0,0)
                else
                  if i < 576 then
                    (35578903,0,0,0)
                  else
                    if i < 577 then
                      (35579927,0,0,0)
                    else
                      (35581975,0,0,0)
              else
                if i < 581 then
                  if i < 579 then
                    (1499192,650,0,0)
                  else
                    if i < 580 then
                      (1499224,651,0,0)
                    else
                      (1499288,652,0,0)
                else
                  if i < 582 then
                    (1499416,653,0,0)
                  else
                    if i < 583 then
                      (1499672,654,0,0)
                    else
                      (1500184,655,0,0)
        else
          if i < 606 then
            if i < 595 then
              if i < 589 then
                if i < 586 then
                  if i < 585 then
                    (1501208,656,0,0)
                  else
                    (1503256,657,0,0)
                else
                  if i < 587 then
                    (1433657,658,0,0)
                  else
                    if i < 588 then
                      (1433689,659,0,0)
                    else
                      (1433753,660,0,0)
              else
                if i < 592 then
                  if i < 590 then
                    (1433881,661,0,0)
                  else
                    if i < 591 then
                      (1434137,662,0,0)
                    else
                      (1434649,663,0,0)
                else
                  if i < 593 then
                    (1435673,664,0,0)
                  else
                    if i < 594 then
                      (1437721,665,0,0)
                    else
                      (5693498,666,0,0)
            else
              if i < 600 then
                if i < 597 then
                  if i < 596 then
                    (5693530,667,0,0)
                  else
                    (5693594,668,0,0)
                else
                  if i < 598 then
                    (5693722,669,0,0)
                  else
                    if i < 599 then
                      (5693978,670,0,0)
                    else
                      (5694490,671,0,0)
              else
                if i < 603 then
                  if i < 601 then
                    (5695514,672,0,0)
                  else
                    if i < 602 then
                      (5697562,673,0,0)
                    else
                      (1302587,674,0,0)
                else
                  if i < 604 then
                    (1302619,675,0,0)
                  else
                    if i < 605 then
                      (1302683,676,0,0)
                    else
                      (1302811,677,0,0)
          else
            if i < 617 then
              if i < 611 then
                if i < 608 then
                  if i < 607 then
                    (1303067,678,0,0)
                  else
                    (1303579,679,0,0)
                else
                  if i < 609 then
                    (1304603,680,0,0)
                  else
                    if i < 610 then
                      (1306651,681,0,0)
                    else
                      (5201980,682,0,0)
              else
                if i < 614 then
                  if i < 612 then
                    (5202012,683,0,0)
                  else
                    if i < 613 then
                      (5202076,684,0,0)
                    else
                      (5202204,685,0,0)
                else
                  if i < 615 then
                    (5202460,686,0,0)
                  else
                    if i < 616 then
                      (5202972,687,0,0)
                    else
                      (5203996,688,0,0)
            else
              if i < 623 then
                if i < 620 then
                  if i < 618 then
                    (5169213,689,0,0)
                  else
                    if i < 619 then
                      (5169245,690,0,0)
                    else
                      (5169309,691,0,0)
                else
                  if i < 621 then
                    (5169437,692,0,0)
                  else
                    if i < 622 then
                      (5169693,693,0,0)
                    else
                      (5170205,694,0,0)
              else
                if i < 626 then
                  if i < 624 then
                    (5171229,695,0,0)
                  else
                    if i < 625 then
                      (5173277,696,0,0)
                    else
                      (18800702,697,0,0)
                else
                  if i < 627 then
                    (18800734,698,0,0)
                  else
                    if i < 628 then
                      (18800798,699,0,0)
                    else
                      (18800926,700,0,0)
      else
        if i < 674 then
          if i < 651 then
            if i < 640 then
              if i < 634 then
                if i < 631 then
                  if i < 630 then
                    (18801182,701,0,0)
                  else
                    (18801694,702,0,0)
                else
                  if i < 632 then
                    (18802718,703,0,0)
                  else
                    if i < 633 then
                      (18804766,704,0,0)
                    else
                      (71163967,705,0,0)
              else
                if i < 637 then
                  if i < 635 then
                    (71163999,706,0,0)
                  else
                    if i < 636 then
                      (71164063,707,0,0)
                    else
                      (71164191,708,0,0)
                else
                  if i < 638 then
                    (71164447,709,0,0)
                  else
                    if i < 639 then
                      (71164959,710,0,0)
                    else
                      (71165983,711,0,0)
            else
              if i < 645 then
                if i < 642 then
                  if i < 641 then
                    (71168031,712,0,0)
                  else
                    (649235,0,0,0)
                else
                  if i < 643 then
                    (1298485,713,0,0)
                  else
                    if i < 644 then
                      (1298517,714,0,0)
                    else
                      (1298581,715,0,0)
              else
                if i < 648 then
                  if i < 646 then
                    (1298709,716,0,0)
                  else
                    if i < 647 then
                      (1298965,717,0,0)
                    else
                      (1299477,718,0,0)
                else
                  if i < 649 then
                    (1300501,719,0,0)
                  else
                    if i < 650 then
                      (2998360,0,0,0)
                    else
                      (2998424,0,0,0)
          else
            if i < 662 then
              if i < 656 then
                if i < 653 then
                  if i < 652 then
                    (2998552,0,0,0)
                  else
                    (2998808,0,0,0)
                else
                  if i < 654 then
                    (2999320,0,0,0)
                  else
                    if i < 655 then
                      (3000344,0,0,0)
                    else
                      (3002392,0,0,0)
              else
                if i < 659 then
                  if i < 657 then
                    (3006488,0,0,0)
                  else
                    if i < 658 then
                      (2867289,0,0,0)
                    else
                      (2867353,0,0,0)
                else
                  if i < 660 then
                    (2867481,0,0,0)
                  else
                    if i < 661 then
                      (2867737,0,0,0)
                    else
                      (2868249,0,0,0)
            else
              if i < 668 then
                if i < 665 then
                  if i < 663 then
                    (2869273,0,0,0)
                  else
                    if i < 664 then
                      (2871321,0,0,0)
                    else
                      (2875417,0,0,0)
                else
                  if i < 666 then
                    (11386970,0,0,0)
                  else
                    if i < 667 then
                      (11387034,0,0,0)
                    else
                      (11387162,0,0,0)
              else
                if i < 671 then
                  if i < 669 then
                    (11387418,0,0,0)
                  else
                    if i < 670 then
                      (11387930,0,0,0)
                    else
                      (11388954,0,0,0)
                else
                  if i < 672 then
                    (11391002,0,0,0)
                  else
                    if i < 673 then
                      (11395098,0,0,0)
                    else
                      (2605147,0,0,0)
        else
          if i < 696 then
            if i < 685 then
              if i < 679 then
                if i < 676 then
                  if i < 675 then
                    (2605211,0,0,0)
                  else
                    (2605339,0,0,0)
                else
                  if i < 677 then
                    (2605595,0,0,0)
                  else
                    if i < 678 then
                      (2606107,0,0,0)
                    else
                      (2607131,0,0,0)
              else
                if i < 682 then
                  if i < 680 then
                    (2609179,0,0,0)
                  else
                    if i < 681 then
                      (2613275,0,0,0)
                    else
                      (10403932,0,0,0)
                else
                  if i < 683 then
                    (10403996,0,0,0)
                  else
                    if i < 684 then
                      (10404124,0,0,0)
                    else
                      (10404380,0,0,0)
            else
              if i < 690 then
                if i < 687 then
                  if i < 686 then
                    (10404892,0,0,0)
                  else
                    (10405916,0,0,0)
                else
                  if i < 688 then
                    (10407964,0,0,0)
                  else
                    if i < 689 then
                      (10338397,0,0,0)
                    else
                      (10338461,0,0,0)
              else
                if i < 693 then
                  if i < 691 then
                    (10338589,0,0,0)
                  else
                    if i < 692 then
                      (10338845,0,0,0)
                    else
                      (10339357,0,0,0)
                else
                  if i < 694 then
                    (10340381,0,0,0)
                  else
                    if i < 695 then
                      (10342429,0,0,0)
                    else
                      (10346525,0,0,0)
          else
            if i < 707 then
              if i < 701 then
                if i < 698 then
                  if i < 697 then
                    (37601374,0,0,0)
                  else
                    (37601438,0,0,0)
                else
                  if i < 699 then
                    (37601566,0,0,0)
                  else
                    if i < 700 then
                      (37601822,0,0,0)
                    else
                      (37602334,0,0,0)
              else
                if i < 704 then
                  if i < 702 then
                    (37603358,0,0,0)
                  else
                    if i < 703 then
                      (37605406,0,0,0)
                    else
                      (37609502,0,0,0)
                else
                  if i < 705 then
                    (142327903,0,0,0)
                  else
                    if i < 706 then
                      (142327967,0,0,0)
                    else
                      (142328095,0,0,0)
            else
              if i < 713 then
                if i < 710 then
                  if i < 708 then
                    (142328351,0,0,0)
                  else
                    if i < 709 then
                      (142328863,0,0,0)
                    else
                      (142329887,0,0,0)
                else
                  if i < 711 then
                    (142331935,0,0,0)
                  else
                    if i < 712 then
                      (142336031,0,0,0)
                    else
                      (2596949,0,0,0)
              else
                if i < 716 then
                  if i < 714 then
                    (2597013,0,0,0)
                  else
                    if i < 715 then
                      (2597141,0,0,0)
                    else
                      (2597397,0,0,0)
                else
                  if i < 717 then
                    (2597909,0,0,0)
                  else
                    if i < 718 then
                      (2598933,0,0,0)
                    else
                      (2600981,0,0,0)

def rows : Table := ⟨719,rowAt⟩

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
theorem rows_checked_288 : verifiedRange rows 288 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_320 : verifiedRange rows 320 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_352 : verifiedRange rows 352 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_384 : verifiedRange rows 384 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_416 : verifiedRange rows 416 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_448 : verifiedRange rows 448 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_480 : verifiedRange rows 480 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_512 : verifiedRange rows 512 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_544 : verifiedRange rows 544 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_576 : verifiedRange rows 576 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_608 : verifiedRange rows 608 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_640 : verifiedRange rows 640 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_672 : verifiedRange rows 672 32=true := by decide

set_option maxHeartbeats 10000000 in
theorem rows_checked_704 : verifiedRange rows 704 15=true := by decide

theorem rows_verified : verified rows=true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hbound : i < 719 := List.mem_range.mp hi
  by_cases h352 : i < 352
  · by_cases h160 : i < 160
    · by_cases h64 : i < 64
      · by_cases h32 : i < 32
        · exact verifiedRange_at rows 0 32 rows_checked_0 i (by omega) (by omega)
        · exact verifiedRange_at rows 32 32 rows_checked_32 i (by omega) (by omega)
      · by_cases h96 : i < 96
        · exact verifiedRange_at rows 64 32 rows_checked_64 i (by omega) (by omega)
        · by_cases h128 : i < 128
          · exact verifiedRange_at rows 96 32 rows_checked_96 i (by omega) (by omega)
          · exact verifiedRange_at rows 128 32 rows_checked_128 i (by omega) (by omega)
    · by_cases h256 : i < 256
      · by_cases h192 : i < 192
        · exact verifiedRange_at rows 160 32 rows_checked_160 i (by omega) (by omega)
        · by_cases h224 : i < 224
          · exact verifiedRange_at rows 192 32 rows_checked_192 i (by omega) (by omega)
          · exact verifiedRange_at rows 224 32 rows_checked_224 i (by omega) (by omega)
      · by_cases h288 : i < 288
        · exact verifiedRange_at rows 256 32 rows_checked_256 i (by omega) (by omega)
        · by_cases h320 : i < 320
          · exact verifiedRange_at rows 288 32 rows_checked_288 i (by omega) (by omega)
          · exact verifiedRange_at rows 320 32 rows_checked_320 i (by omega) (by omega)
  · by_cases h544 : i < 544
    · by_cases h448 : i < 448
      · by_cases h384 : i < 384
        · exact verifiedRange_at rows 352 32 rows_checked_352 i (by omega) (by omega)
        · by_cases h416 : i < 416
          · exact verifiedRange_at rows 384 32 rows_checked_384 i (by omega) (by omega)
          · exact verifiedRange_at rows 416 32 rows_checked_416 i (by omega) (by omega)
      · by_cases h480 : i < 480
        · exact verifiedRange_at rows 448 32 rows_checked_448 i (by omega) (by omega)
        · by_cases h512 : i < 512
          · exact verifiedRange_at rows 480 32 rows_checked_480 i (by omega) (by omega)
          · exact verifiedRange_at rows 512 32 rows_checked_512 i (by omega) (by omega)
    · by_cases h640 : i < 640
      · by_cases h576 : i < 576
        · exact verifiedRange_at rows 544 32 rows_checked_544 i (by omega) (by omega)
        · by_cases h608 : i < 608
          · exact verifiedRange_at rows 576 32 rows_checked_576 i (by omega) (by omega)
          · exact verifiedRange_at rows 608 32 rows_checked_608 i (by omega) (by omega)
      · by_cases h672 : i < 672
        · exact verifiedRange_at rows 640 32 rows_checked_640 i (by omega) (by omega)
        · by_cases h704 : i < 704
          · exact verifiedRange_at rows 672 32 rows_checked_672 i (by omega) (by omega)
          · exact verifiedRange_at rows 704 15 rows_checked_704 i (by omega) (by omega)

theorem initial_member (w : List Bool) (hw : w ∈ endpointWords) : Member rows ⟨w,w,0⟩ := by
  simp only [endpointWords, Recaman.ThreeNonsuppliedData.endpointWords, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
  · subst w; exact ⟨0, by decide, by decide⟩
  · subst w; exact ⟨1, by decide, by decide⟩
  · subst w; exact ⟨2, by decide, by decide⟩
  · subst w; exact ⟨3, by decide, by decide⟩
  · subst w; exact ⟨4, by decide, by decide⟩
  · subst w; exact ⟨5, by decide, by decide⟩
  · subst w; exact ⟨6, by decide, by decide⟩
  · subst w; exact ⟨7, by decide, by decide⟩
  · subst w; exact ⟨8, by decide, by decide⟩
  · subst w; exact ⟨9, by decide, by decide⟩
  · subst w; exact ⟨10, by decide, by decide⟩
  · subst w; exact ⟨11, by decide, by decide⟩
  · subst w; exact ⟨12, by decide, by decide⟩
  · subst w; exact ⟨13, by decide, by decide⟩
  · subst w; exact ⟨14, by decide, by decide⟩
  · subst w; exact ⟨15, by decide, by decide⟩

end Recaman.SixteenRootAreaData
