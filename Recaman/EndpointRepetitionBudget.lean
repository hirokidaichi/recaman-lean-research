import Recaman.LowSSEndpoint

namespace Recaman.EndpointRepetitionBudget

open LeadingRunSupply OneSSMultiplicity LowSSEndpoint

/-! Reusing one old endpoint costs two additional SS edges each time.
Witnesses need not be minimum; the sharp family deliberately is not. -/

theorem ssCount_append_superadditive (u v : List Bool) :
    ssCount u+ssCount v≤ssCount (u++v) := by
  induction u with
  | nil => simp [ssCount]
  | cons b u ih =>
    cases u with
    | nil => simp [ssCount]
    | cons c u => cases b <;> cases c <;> simp [ssCount] at ih ⊢ <;> omega

theorem intervening_cost (v u : List Bool)
    (hnew : P2 ((v++[true])++u)) (hold : P2 u) : 2≤ssCount (v++[true]) := by
  by_cases hs : 2≤ssCount (v++[true])
  · exact hs
  · have hM := moment_ending_A v (by omega)
    have heq := moment_append (v++[true]) u
    rw [hnew.2,hold.2,hold.1] at heq
    omega

theorem stream_SS_increment (e : Int → Bool) (t : Int) (k d : Nat)
    (hk : 0<k) (hA : e t=true)
    (hnew : ShortPeriodicSupply.P2 e (t+k) (k+d))
    (hold : ShortPeriodicSupply.P2 e t d) :
    ssCount (past e t d)+2≤ssCount (past e (t+k) (k+d)) := by
  have hklen : k=(k-1)+1 := by omega
  have hlast : past e (t+k-(k-1 : Nat)) 1=[true] := by
    have htime : t+(k : Int)-((k-1 : Nat) : Int)-1=t := by omega
    simpa [past,htime] using congrArg (fun b => [b]) hA
  have hfirst : past e (t+k) k=past e (t+k) (k-1)++[true] := by
    calc
      past e (t+k) k = past e (t+k) ((k-1)+1) := congrArg (past e (t+k)) hklen
      _ = past e (t+k) (k-1)++past e (t+k-(k-1 : Nat)) 1 := past_append _ _ _ _
      _ = past e (t+k) (k-1)++[true] := by rw [hlast]
  have htime : t+(k : Int)-k=t := by omega
  have hn := (past_p2_iff e (t+k) (k+d)).mpr hnew
  rw [past_append,hfirst,htime] at hn ⊢
  have hc := intervening_cost _ _ hn ((past_p2_iff e t d).mpr hold)
  have ha := ssCount_append_superadditive (past e (t+k) (k-1)++[true]) (past e t d)
  omega

/-- All supplied windows here end at sign time zero. m+1 distinct A
sources force 2m SS in the largest actual window. -/
theorem repeated_endpoint_budget (e : Int → Bool) (f : Nat → Nat) (m : Nat)
    (hinc : ∀ i : Nat, i<m → f i<f (i+1))
    (hA : ∀ i : Nat, i≤m → e (f i)=true)
    (hP : ∀ i : Nat, i≤m → ShortPeriodicSupply.P2 e (f i) (f i)) :
    2*m≤ssCount (past e (f m) (f m)) := by
  induction m with
  | zero => omega
  | succ m ih =>
    have hi := ih (fun i hi => hinc i (by omega))
      (fun i hi => hA i (by omega)) (fun i hi => hP i (by omega))
    have hstep := hinc m (by omega)
    let k := f (m+1)-f m
    have hk : 0<k := by dsimp [k]; omega
    have ht : (f m : Int)+k=f (m+1) := by dsimp [k]; omega
    have hd : k+f m=f (m+1) := by dsimp [k]; omega
    have hc := stream_SS_increment e (f m) k (f m) hk (hA m (by omega))
      (by rw [ht,hd]; exact hP (m+1) (by omega)) (hP m (by omega))
    rw [ht,hd] at hc
    omega

def block : List Bool :=
  [true,true,false,true,false,true,false,true,false,false,false,true]

def window : Nat → List Bool
  | 0 => [true,true,false]
  | k+1 => block++window k

theorem block_data : block.length=12 ∧ mass block=0 ∧ moment block= -12 := by decide

theorem block_SS (w : List Bool) : ssCount (block++w)=2+ssCount w := by
  simp [block,ssCount]
  omega

theorem window_length (k : Nat) : (window k).length=12*k+3 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [window,block,ih]; omega

theorem window_P2 (k : Nat) : P2 (window k) := by
  induction k with
  | zero => unfold P2 window; decide
  | succ k ih =>
    unfold window
    constructor
    · rw [mass_append,block_data.2.1,ih.1]; rfl
    · rw [moment_append,block_data.2.2,ih.2,block_data.1,ih.1]; rfl

theorem window_SS (k : Nat) : ssCount (window k)=2*k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [window,block_SS,ih]; omega

theorem window_starts_AA (k : Nat) : ∃ v : List Bool, window k=true::true::v := by
  cases k with
  | zero => exact ⟨[false],rfl⟩
  | succ k => exact ⟨[false,true,false,true,false,true,false,false,false,true]++window k,rfl⟩

theorem window_noSAAS (k : Nat) : SSFreeSupply.NoSAAS (true::window k) := by
  have hz : saasCount (window k)=0 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      obtain ⟨v,hv⟩ := window_starts_AA k
      simp [window,block,hv,saasCount] at ih ⊢
      omega
  intro u v heq
  have hc := saas_occurrence_positive u v
  have hz' : saasCount (true::window k)=0 := by simpa [saasCount] using hz
  rw [← heq,hz'] at hc
  omega

theorem source_A (K r : Nat) (hr : r≤K) : (true::window K)[12*r]?=some true := by
  induction K generalizing r with
  | zero =>
    have hr0 : r=0 := by omega
    subst r
    rfl
  | succ K ih =>
    cases r with
    | zero => rfl
    | succ r =>
      let pre : List Bool := [true,true,true,false,true,false,true,false,true,false,false,false]
      have heq : true::window (K+1)=pre++(true::window K) := rfl
      rw [heq,List.getElem?_append_right (by simp [pre]; omega)]
      have hidx : 12*(r+1)-pre.length=12*r := by simp [pre]; omega
      rw [hidx]
      exact ih r (by omega)

theorem sources_distinct (K k j : Nat) (hk : k≤K) (hj : j≤K)
    (heq : 12*(K-k)=12*(K-j)) : k=j := by omega

theorem common_endpoint_position (K k : Nat) (hk : k≤K) :
    12*(K-k)+(window k).length=(window K).length := by
  rw [window_length,window_length]
  omega

theorem suffix_embedding (k r : Nat) :
    ∃ u : List Bool, window (k+r)=u++window k ∧ u.length=12*r := by
  induction r with
  | zero => exact ⟨[],by simp,by simp⟩
  | succ r ih =>
    obtain ⟨u,hw,hu⟩ := ih
    refine ⟨block++u,?_,?_⟩
    · have hidx : k+(r+1)=(k+r)+1 := by omega
      rw [hidx,window,hw,List.append_assoc]
    · simp [hu,block]; omega

/-- An exact common history attaining two SS per additional source.
All chosen windows share the final endpoint, and every current sign is A. -/
theorem sharp_common_history (K : Nat) :
    ssCount (window K)=2*K ∧ SSFreeSupply.NoSAAS (true::window K) ∧
    ∀ k : Nat, k≤K → P2 (window k) ∧
      (true::window K)[12*(K-k)]?=some true ∧
      ∃ u : List Bool, window K=u++window k ∧ u.length=12*(K-k) := by
  refine ⟨window_SS K,window_noSAAS K,?_⟩
  intro k hk
  refine ⟨window_P2 k,source_A K (K-k) (by omega),?_⟩
  have h := suffix_embedding k (K-k)
  have heq : k+(K-k)=K := by omega
  rwa [heq] at h

/-- Every source has the lag-three low-SS witness AAS. It is strictly
shorter than the chosen common-endpoint window when k is positive. -/
theorem family_has_lag_three (k : Nat) : (window k).take 3=[true,true,false] ∧
    P2 ((window k).take 3) := by
  cases k <;> simp [window,block,P2,mass_cons,moment,ShortPeriodicSupply.sign]

theorem family_nonminimum (k : Nat) (hk : 0<k) :
    3<(window k).length ∧ P2 ((window k).take 3) := by
  exact ⟨by rw [window_length]; omega,(family_has_lag_three k).2⟩

end Recaman.EndpointRepetitionBudget
