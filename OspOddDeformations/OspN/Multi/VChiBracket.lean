import OspOddDeformations.OspN.Multi.ThetaStarBracket
import OspOddDeformations.OspN.Multi.R1

/-!
# `V_γ` intertwines `[·,·]_β` with `[·,·]_{J-Ω}` (statement (ii) of `Multi/FactorDefs.lean`)
-/

-- Toolchain (v4.34): `OspBasis` is a plain `def` whose sum structure the proofs use; as in
-- `ThetaStarBracket.lean`, restore the pre-v4.34 type-transparency behaviour of `isDefEq` here.
set_option backward.isDefEq.respectTransparency.types false

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

/-- The data of the deformed bracket (5.3) on basis symbols, as an element of `𝔤_{R_r}`:
`[X,Y]_0 + Σ_s κ_s Γ^{(s)}(X,Y)`. -/
noncomputable def Bbeta (Z Z' : OspBasis F n) : RModM F n r :=
  B0data Z Z' + ∑ s : Fin r, gsmul (gmono {s} 1) (kap ∅ (GammaSBasis s Z Z'))

theorem grComp_kap_empty (w : OspBasis F n → PmnR F n r) (V : OspBasis F n) :
    grComp (kap ∅ w) V = w V • gone := by
  funext T
  by_cases h : T = ∅ <;> simp [grComp, kap, gone, h]

theorem bracketBetaM_eq_liftB : bracketBetaM (F := F) (n := n) (r := r) = liftB Bbeta := by
  funext x y
  refine RModM_ext_grComp fun V => ?_
  rw [grComp_bracketBetaM, grComp_liftB, grComp_bracket0M]
  simp only [Bbeta, grComp_add, grComp_sum, grComp_gsmul, grComp_kap_empty, B0data, grComp_gtens,
    gmul_add_right, gmul_sum_right, gmul_smul_right, gmul_gone, Finset.sum_add_distrib]
  refine congrArg₂ (· + ·) ?_ ?_
  · exact Finset.sum_congr rfl fun Z _ => Finset.sum_congr rfl fun Z' _ => rfl
  · rw [sum_perm3]
    rfl

/-- `Σ_s κ_s ⊗ (v with β ↦ β^{(s)})`. -/
noncomputable def PhiG (v : OspMod F n) : RModM F n r :=
  ∑ s : Fin r, gsmul (gmono {s} 1) (kap ∅ (liftBy (embS s) v))

theorem Bbeta_eq_PhiG (Z Z' : OspBasis F n) :
    Bbeta (F := F) (n := n) (r := r) Z Z' = B0data Z Z' + PhiG (GammaBasis Z Z') := rfl

theorem gmono_eq_smul (S : Finset (Fin r)) (c : PmnR F n r) : gmono S c = c • gmono S 1 := by
  funext T; by_cases h : T = S <;> simp [gmono, h]

theorem grComp_PhiG (v : OspMod F n) (V : OspBasis F n) :
    grComp (PhiG (r := r) v) V = ∑ s : Fin r, embS s (v V) • gmono {s} 1 := by
  unfold PhiG
  rw [grComp_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [grComp_gsmul, grComp_kap_empty, gmul_smul_right, gmul_gone]
  rfl

theorem PhiG_add (v w : OspMod F n) : PhiG (r := r) (v + w) = PhiG v + PhiG w := by
  refine RModM_ext_grComp fun V => ?_
  rw [grComp_add, grComp_PhiG, grComp_PhiG, grComp_PhiG, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [add_smul]

theorem PhiG_neg (v : OspMod F n) : PhiG (r := r) (-v) = - PhiG v := by
  refine RModM_ext_grComp fun V => ?_
  rw [show grComp (-PhiG (r := r) v) V = - grComp (PhiG v) V from rfl, grComp_PhiG, grComp_PhiG,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [neg_smul]

theorem PhiG_sub (v w : OspMod F n) : PhiG (r := r) (v - w) = PhiG v - PhiG w := by
  rw [sub_eq_add_neg, PhiG_add, PhiG_neg, ← sub_eq_add_neg]

theorem PhiG_rsmul (q : ℚ) (v : OspMod F n) : PhiG (r := r) (q • v) = q • PhiG v := by
  refine RModM_ext_grComp fun V => ?_
  rw [show grComp (q • PhiG (r := r) v) V = q • grComp (PhiG v) V from rfl, grComp_PhiG,
    grComp_PhiG, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [smul_assoc]

theorem PhiG_beta (u : I n) (i : F.K) (w : OspMod F n) (hw : ∀ W, IsQ (w W)) :
    PhiG (r := r) (beta F n u i • w) = gtens (gammaR u i) w := by
  refine RModM_ext_grComp fun V => ?_
  rw [grComp_PhiG, grComp_gtens]
  have e : gammaR (F := F) (n := n) (r := r) u i =
      ∑ s : Fin r, betaR F n r s u i • gmono {s} 1 := by
    unfold gammaR
    exact Finset.sum_congr rfl fun s _ => gmono_eq_smul _ _
  rw [e, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hb : embS (F := F) (n := n) s (beta F n u i) = betaR F n r s u i := by
    simp [embS, beta, betaR, MvPolynomial.rename_X]
  rw [ospMod_smul_apply, map_mul, emb0_eq_embS (hw V) s, hb, smul_smul, mul_comm]

theorem VBasis0_parity (X W : OspBasis F n) :
    HasParity (parity X + parity W) (grComp (VBasis0 (gammaR (F := F) (n := n) (r := r)) X) W) := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h1 : ∀ u i, HasParity (1 : ZMod 2) (gammaR (F := F) (n := n) (r := r) u i) :=
    fun u i => by simpa using (HasCard_gammaR (F := F) (n := n) (r := r) u i).parity
  rcases X with ⟨⟨u, v⟩, h⟩ | ⟨⟨i, j⟩, h⟩ | ⟨u, i⟩
  · have h0 : parity (Sum.inl ⟨(u, v), h⟩ : OspBasis F n) = 0 := rfl
    rw [h0, zero_add]
    simp only [VBasis0, grComp_add, grComp_sub, grComp_rsmul, grComp_sum, grComp_gtens]
    refine (HasParity.add (HasParity.smul_of (HasCard_gone (F := F) (n := n) (r := r)).parity _
      fun hc => ?_) (HasParity.sum _ fun i _ => HasParity.add ?_ ?_)).sub
      (HasParity.rsmul _ (HasParity.sum _ fun i _ => HasParity.sum _ fun j _ => ?_))
    · rw [parity_of_emb0_eN hc, parity_Lof]; simp
    · refine HasParity.smul_of (h1 v (F.dual i)) _ fun hc => ?_
      rw [parity_of_emb0_eN hc, parity_Fof]
    · refine HasParity.smul_of (h1 u (F.dual i)) _ fun hc => ?_
      rw [parity_of_emb0_eN hc, parity_Fof]
    · refine HasParity.smul_of ((h1 u (F.dual i)).gmul (h1 v (F.dual j))) _ fun hc => ?_
      rw [parity_of_emb0_Sof hc]; simp [h11]
  · have h0 : parity (Sum.inr (Sum.inl ⟨(i, j), h⟩) : OspBasis F n) = 0 := rfl
    rw [h0, zero_add]
    simp only [VBasis0, grComp_gtens]
    refine HasParity.smul_of (HasCard_gone (F := F) (n := n) (r := r)).parity _ fun hc => ?_
    rw [parity_of_emb0_Sof hc]; simp
  · have h0 : parity (Sum.inr (Sum.inr (u, i)) : OspBasis F n) = 1 := rfl
    rw [h0]
    simp only [VBasis0, grComp_add, grComp_rsmul, grComp_sum, grComp_gtens]
    refine (HasParity.smul_of (HasCard_gone (F := F) (n := n) (r := r)).parity _ fun hc => ?_).add
      (HasParity.rsmul _ (HasParity.sum _ fun j _ => ?_))
    · rw [parity_of_emb0_eN hc, parity_Fof]; simp [h11]
    · refine HasParity.smul_of (h1 u (F.dual j)) _ fun hc => ?_
      rw [parity_of_emb0_Sof hc]; simp

/-! ### `bracket0` against `Sof`, all orders -/

theorem Sof_eq_zero {i j : F.K} (h : F.key i = F.key j) : (Sof i j : OspMod F n) = 0 := by
  unfold Sof
  have h1 : ¬ F.key i < F.key j := by omega
  have h2 : ¬ F.key j < F.key i := by omega
  simp only [h1, h2, ↓reduceDIte]

theorem bracketSS_swap12 (i j k l : F.K) :
    (bracketSS i j k l : OspMod F n) = -bracketSS j i k l := by
  unfold bracketSS; abel

theorem bracketSS_diag_left (a k l : F.K) : (bracketSS a a k l : OspMod F n) = 0 := by
  unfold bracketSS; abel

theorem bracket0_Fof_Sof_gen (a : I n) (i j k : F.K) :
    bracket0 (eN (Fof a i) : OspMod F n) (Sof j k) = - bracketSF j k a i := by
  rcases lt_trichotomy (F.key j) (F.key k) with h | h | h
  · exact bracket0_Fof_Sof a i j k h
  · rw [Sof_eq_zero h, bracket0_zero_right, F.key_injective h, bracketSF_diag, neg_zero]
  · rw [Sof_antisymm j k, bracket0_neg_right, bracket0_Fof_Sof a i k j h, neg_neg,
      bracketSF_swap12 j k, neg_neg]

theorem bracket0_Sof_Fof_gen (j k : F.K) (a : I n) (i : F.K) :
    bracket0 (Sof j k : OspMod F n) (eN (Fof a i)) = bracketSF j k a i := by
  rcases lt_trichotomy (F.key j) (F.key k) with h | h | h
  · exact bracket0_Sof_Fof j k h a i
  · rw [Sof_eq_zero h, bracket0_zero_left, F.key_injective h, bracketSF_diag]
  · rw [Sof_antisymm j k, bracket0_neg_left, bracket0_Sof_Fof k j h a i, bracketSF_swap12 j k]

theorem bracket0_Sof_Sof_gen (i j k l : F.K) :
    bracket0 (Sof i j : OspMod F n) (Sof k l) = bracketSS i j k l := by
  rcases lt_trichotomy (F.key i) (F.key j) with h | h | h
  · rw [Sof_of_lt h]; exact bracket0_S_Sof i j h k l
  · rw [Sof_eq_zero h, bracket0_zero_left, F.key_injective h, bracketSS_diag_left]
  · rw [Sof_antisymm i j, bracket0_neg_left, Sof_of_lt h, bracket0_S_Sof j i h k l,
      bracketSS_swap12 i j]

/-! ### `bracketJBasis0` against `S`-symbols is `J`-free -/

/-- `W` is an `S`-symbol. -/
def IsSsym (W : OspBasis F n) : Prop :=
  ∃ (i j : F.K) (h : F.key i < F.key j), W = Sum.inr (Sum.inl ⟨(i, j), h⟩)

theorem Sof_support {k l : F.K} {W : OspBasis F n}
    (h : emb0 (F := F) (n := n) (r := r) (Sof k l W) ≠ 0) : IsSsym W := by
  unfold Sof at h
  split_ifs at h with h1 h2
  · have := parity_of_emb0_eN h
    exact ⟨k, l, h1, this⟩
  · have h' : emb0 (F := F) (n := n) (r := r) ((eN (Sum.inr (Sum.inl ⟨(l, k), h2⟩) :
        OspBasis F n) : OspMod F n) W) ≠ 0 := by
      intro hh; apply h; simp only [Pi.neg_apply, map_neg, hh, neg_zero]
    exact ⟨l, k, h2, parity_of_emb0_eN h'⟩
  · exact absurd (map_zero _) h

theorem bracketJBasis0_S_left (J' : I n → I n → GR F n r) {W : OspBasis F n} (hW : IsSsym W)
    (W' : OspBasis F n) : bracketJBasis0 J' W W' = B0data W W' := by
  obtain ⟨i, j, h, rfl⟩ := hW
  rcases W' with ⟨⟨u, v⟩, h2⟩ | ⟨⟨k, l⟩, h2⟩ | ⟨w, m⟩
  · unfold B0data; simp [bracketJBasis0, bracket0Basis, gtens_zero_right]
  · rfl
  · rfl

theorem bracketJBasis0_S_right (J' : I n → I n → GR F n r) (W : OspBasis F n) {W' : OspBasis F n}
    (hW : IsSsym W') : bracketJBasis0 J' W W' = B0data W W' := by
  obtain ⟨i, j, h, rfl⟩ := hW
  rcases W with ⟨⟨u, v⟩, h2⟩ | ⟨⟨k, l⟩, h2⟩ | ⟨w, m⟩
  · unfold B0data; simp [bracketJBasis0, bracket0Basis, gtens_zero_right]
  · rfl
  · unfold B0data; simp [bracketJBasis0, bracket0Basis, gtens_neg_right]

theorem liftB_congr_left (B B' : OspBasis F n → OspBasis F n → RModM F n r) (x y : RModM F n r)
    (h : ∀ p : RBasisM F n r, x p ≠ 0 → ∀ Z', B p.1 Z' = B' p.1 Z') :
    liftB B x y = liftB B' x y := by
  unfold liftB
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  by_cases hp : x p = 0
  · simp [hp]
  · rw [h p hp q.1]

theorem liftB_congr_right (B B' : OspBasis F n → OspBasis F n → RModM F n r) (x y : RModM F n r)
    (h : ∀ q : RBasisM F n r, y q ≠ 0 → ∀ Z, B Z q.1 = B' Z q.1) :
    liftB B x y = liftB B' x y := by
  unfold liftB
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : y q = 0
  · simp [hq]
  · rw [h q hq p.1]

theorem gtens_support {a : GR F n r} {v : OspMod F n} {p : RBasisM F n r}
    (h : gtens a v p ≠ 0) : emb0 (F := F) (n := n) (r := r) (v p.1) ≠ 0 := by
  intro hh; apply h; rw [gtens_apply, hh, mul_zero]

theorem liftBJ_S_left (J' : I n → I n → GR F n r) (a : GR F n r) (k l : F.K) (y : RModM F n r) :
    liftB (bracketJBasis0 J') (gtens a (Sof k l)) y = liftB B0data (gtens a (Sof k l)) y :=
  liftB_congr_left _ _ _ _ fun _ hp Z' =>
    bracketJBasis0_S_left J' (Sof_support (gtens_support hp)) Z'

theorem liftBJ_S_right (J' : I n → I n → GR F n r) (a : GR F n r) (k l : F.K) (x : RModM F n r) :
    liftB (bracketJBasis0 J') x (gtens a (Sof k l)) = liftB B0data x (gtens a (Sof k l)) :=
  liftB_congr_right _ _ _ _ fun _ hq Z =>
    bracketJBasis0_S_right J' Z (Sof_support (gtens_support hq))

theorem sum2_emb0_eN (B : OspBasis F n → OspBasis F n → RModM F n r) (b b' : OspBasis F n) :
    ∑ W : OspBasis F n, ∑ W' : OspBasis F n,
      (emb0 (F := F) (n := n) (r := r) (eN b W) * emb0 (eN b' W')) • B W W' = B b b' := by
  rw [Finset.sum_eq_single b]
  · rw [Finset.sum_eq_single b']
    · rw [emb0_eN, emb0_eN, ite_eq_left rfl, ite_eq_left rfl, mul_one, one_smul]
    · intro W' _ hW'
      rw [emb0_eN, emb0_eN, ite_eq_right hW', mul_zero, zero_smul]
    · simp
  · intro W _ hW
    refine Finset.sum_eq_zero fun W' _ => ?_
    rw [emb0_eN, ite_eq_right hW, zero_mul, zero_smul]
  · simp

theorem liftBJ_eN_eN (J' : I n → I n → GR F n r) (a a' : GR F n r) (b b' : OspBasis F n) :
    liftB (bracketJBasis0 J') (gtens a (eN b)) (gtens a' (eN b')) =
      gsmul (gmul a (sigPow (parity b) a')) (bracketJBasis0 J' b b') := by
  have hv : ∀ W, emb0 (F := F) (n := n) (r := r) (eN b W) ≠ 0 → parity W = parity b :=
    fun W h => by rw [hv_eN b W h]
  rw [liftB_gtens (bracketJBasis0 J') a a' (eN b) (eN b') (parity b) hv, sum2_emb0_eN]

theorem hv_Sof' (k l : F.K) :
    ∀ W, emb0 (F := F) (n := n) (r := r) (Sof k l W) ≠ 0 → parity W = 0 := hv_Sof k l

theorem liftBJ_Sof_eN (J' : I n → I n → GR F n r) (a a' : GR F n r) (k l : F.K)
    (b' : OspBasis F n) :
    liftB (bracketJBasis0 J') (gtens a (Sof k l)) (gtens a' (eN b')) =
      gtens (gmul a a') (bracket0 (Sof k l) (eN b')) := by
  rw [liftBJ_S_left, liftB0_gtens a a' (Sof k l) (eN b') 0 (hv_Sof' k l), sigPow_zero]

theorem liftB0_gtens_eN_Sof (a a' : GR F n r) (b : OspBasis F n) (k l : F.K) :
    liftB B0data (gtens a (eN b)) (gtens a' (Sof k l)) =
      gtens (gmul a (sigPow (parity b) a')) (bracket0 (eN b) (Sof k l)) :=
  liftB0_gtens a a' (eN b) (Sof k l) (parity b) (fun W h => by rw [hv_eN b W h])

theorem liftBJ_eN_Sof (J' : I n → I n → GR F n r) (a a' : GR F n r) (b : OspBasis F n)
    (k l : F.K) :
    liftB (bracketJBasis0 J') (gtens a (eN b)) (gtens a' (Sof k l)) =
      gtens (gmul a (sigPow (parity b) a')) (bracket0 (eN b) (Sof k l)) := by
  rw [liftBJ_S_right]
  exact liftB0_gtens_eN_Sof a a' b k l

theorem liftBJ_Sof_Sof (J' : I n → I n → GR F n r) (a a' : GR F n r) (i j k l : F.K) :
    liftB (bracketJBasis0 J') (gtens a (Sof i j)) (gtens a' (Sof k l)) =
      gtens (gmul a a') (bracket0 (Sof i j) (Sof k l)) := by
  rw [liftBJ_S_left, liftB0_gtens a a' (Sof i j) (Sof k l) 0 (hv_Sof' i j), sigPow_zero]

theorem PhiG_zero : PhiG (r := r) (0 : OspMod F n) = 0 := by
  refine RModM_ext_grComp fun V => ?_
  rw [grComp_PhiG]
  change _ = (0 : GR F n r)
  simp

theorem extT_bracketSS' (A0 : OspBasis F n → RModM F n r) (hS : SCompat A0) (i j k l : F.K) :
    extT A0 (bracketSS i j k l : OspMod F n) = gtens gone (bracketSS i j k l : OspMod F n) := by
  unfold bracketSS
  simp only [extT_add, extT_sub, extT_rsmul, extT_Sof _ hS, gtens_add_right, gtens_sub_right,
    gtens_rsmul_right]

theorem VBasis0_SCompat : SCompat (VBasis0 (gammaR (F := F) (n := n) (r := r))) :=
  fun _ _ _ => rfl

theorem VecSS2 (i j k l : F.K) (h1 : F.key i < F.key j) (h2 : F.key k < F.key l) :
    liftB (bracketJBasis0 JmOmega) (VBasis0 (gammaR (F := F) (n := n) (r := r))
        (Sum.inr (Sum.inl ⟨(i, j), h1⟩)))
      (VBasis0 gammaR (Sum.inr (Sum.inl ⟨(k, l), h2⟩))) =
    linM (VBasis0 gammaR)
      (Bbeta (Sum.inr (Sum.inl ⟨(i, j), h1⟩)) (Sum.inr (Sum.inl ⟨(k, l), h2⟩))) := by
  change liftB (bracketJBasis0 JmOmega) (gtens gone (Sof i j)) (gtens gone (Sof k l)) =
    linM (VBasis0 gammaR) (B0data _ _ + PhiG 0)
  rw [liftBJ_Sof_Sof, PhiG_zero, add_zero]
  change _ = linM (VBasis0 gammaR) (gtens gone (bracketSS i j k l))
  rw [linM_gtens', extT_bracketSS' _ VBasis0_SCompat, gsmul_gone, gone_gmul, bracket0_Sof_Sof_gen]

/-! ### Kronecker sums with `g` -/

theorem sum_g_right {M : Type*} [AddCommMonoid M] [Module ℚ M] (k : F.K) (f : F.K → M) :
    ∑ l : F.K, F.g k l • f l = f (F.dual k) := by
  rw [Finset.sum_eq_single (F.dual k)]
  · simp [FermionIndex.g]
  · intro l _ hl; simp [FermionIndex.g, hl]
  · simp

theorem sum_g_left {M : Type*} [AddCommMonoid M] [Module ℚ M] (k : F.K) (f : F.K → M) :
    ∑ l : F.K, F.g l k • f l = f (F.dual k) := by
  simp_rw [F.g_symm _ k]
  exact sum_g_right k f

theorem sum_gtens_g (c : F.K → GR F n r) (k : F.K) (v : OspMod F n) :
    ∑ l : F.K, gtens (c (F.dual l)) (F.g k l • v) = gtens (c k) v := by
  simp_rw [gtens_rsmul_right]
  rw [sum_g_right k (fun l => gtens (c (F.dual l)) v), F.dual_dual]

theorem sum_gtens_g' (c : F.K → GR F n r) (k : F.K) (v : OspMod F n) :
    ∑ l : F.K, gtens (c (F.dual l)) (F.g l k • v) = gtens (c k) v := by
  simp_rw [gtens_rsmul_right]
  rw [sum_g_left k (fun l => gtens (c (F.dual l)) v), F.dual_dual]

theorem extT_bracketSF' (A0 : OspBasis F n → RModM F n r) (j k : F.K) (w : I n) (i : F.K) :
    extT A0 (bracketSF j k w i : OspMod F n) =
      (F.g k i) • A0 (Fof w j) - (F.g j i) • A0 (Fof w k) := by
  unfold bracketSF
  rw [extT_sub, extT_rsmul, extT_rsmul, extT_eN, extT_eN]

theorem sum_bracketSS_gtens (c : F.K → GR F n r) (j k i : F.K) :
    ∑ x : F.K, gtens (c (F.dual x)) (bracketSS j k x i : OspMod F n) =
      gtens (c k) (Sof j i) - gtens (c j) (Sof k i) +
        F.g k i • ∑ x : F.K, gtens (c (F.dual x)) (Sof x j) -
        F.g j i • ∑ x : F.K, gtens (c (F.dual x)) (Sof x k) := by
  have h3 : ∀ x : F.K, (Sof j x : OspMod F n) = -Sof x j := fun x => Sof_antisymm j x
  have h4 : ∀ x : F.K, (Sof k x : OspMod F n) = -Sof x k := fun x => Sof_antisymm k x
  unfold bracketSS
  simp only [gtens_add_right, gtens_sub_right, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_gtens_g]
  simp only [gtens_rsmul_right, h3, h4, gtens_neg_right, Finset.sum_neg_distrib, Finset.smul_sum,
    smul_neg]
  abel

theorem V0_F (u : I n) (i : F.K) :
    VBasis0 (gammaR (F := F) (n := n) (r := r)) (Fof u i) =
      gtens gone (eN (Fof u i)) + (1 / 2 : ℚ) • ∑ j : F.K, gtens (gammaR u (F.dual j)) (Sof j i) :=
  rfl

theorem VecSF2 (j k : F.K) (h : F.key j < F.key k) (w : I n) (i : F.K) :
    liftB (bracketJBasis0 JmOmega) (VBasis0 (gammaR (F := F) (n := n) (r := r))
        (Sum.inr (Sum.inl ⟨(j, k), h⟩))) (VBasis0 gammaR (Fof w i)) =
    linM (VBasis0 gammaR) (Bbeta (Sum.inr (Sum.inl ⟨(j, k), h⟩)) (Fof w i)) := by
  change liftB (bracketJBasis0 JmOmega) (gtens gone (Sof j k))
    (gtens gone (eN (Fof w i)) + (1 / 2 : ℚ) • ∑ l : F.K, gtens (gammaR w (F.dual l)) (Sof l i)) =
    linM (VBasis0 gammaR) (B0data _ _ + PhiG (GammaSF j k w i))
  simp only [liftB_add_right, liftB_rsmul_right, liftB_sum_right, liftBJ_Sof_eN, liftBJ_Sof_Sof,
    gone_gmul, bracket0_Sof_Fof_gen, bracket0_Sof_Sof_gen]
  have e1 : B0data (r := r) (Sum.inr (Sum.inl ⟨(j, k), h⟩) : OspBasis F n) (Fof w i) =
      gtens gone (bracketSF j k w i) := rfl
  have e2 : PhiG (r := r) (GammaSF j k w i : OspMod F n) =
      (1 / 2 : ℚ) • (gtens (gammaR (r := r) w k) (Sof j i) - gtens (gammaR w j) (Sof k i)) := by
    unfold GammaSF
    rw [PhiG_rsmul, PhiG_sub, PhiG_beta _ _ _ (fun W => IsQ_Sof _ _ W),
      PhiG_beta _ _ _ (fun W => IsQ_Sof _ _ W)]
  rw [e1, e2]
  simp only [linM_add, linM_rsmul, linM_sub, linM_gtens', extT_bracketSF',
    extT_Sof _ VBasis0_SCompat, gsmul_gone_gtens, gsmul_gone]
  rw [sum_bracketSS_gtens]
  simp only [V0_F, bracketSF, gtens_sub_right, gtens_rsmul_right, smul_sub, smul_add,
    Finset.smul_sum]
  simp only [smul_comm (F.g k i) (1 / 2 : ℚ), smul_comm (F.g j i) (1 / 2 : ℚ)]
  abel

theorem sum_bracketSS_gtens2 (c : F.K → GR F n r) (i j k : F.K) :
    ∑ x : F.K, gtens (c (F.dual x)) (bracketSS x i j k : OspMod F n) =
      F.g i j • ∑ x : F.K, gtens (c (F.dual x)) (Sof x k) - gtens (c j) (Sof i k) -
        F.g i k • ∑ x : F.K, gtens (c (F.dual x)) (Sof x j) + gtens (c k) (Sof i j) := by
  unfold bracketSS
  simp only [gtens_add_right, gtens_sub_right, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_gtens_g']
  simp only [gtens_rsmul_right, Finset.smul_sum]

theorem liftB_sub_right (B0 : OspBasis F n → OspBasis F n → RModM F n r) (x y y' : RModM F n r) :
    liftB B0 x (y - y') = liftB B0 x y - liftB B0 x y' := by
  rw [sub_eq_add_neg, liftB_add_right, liftB_neg_right, ← sub_eq_add_neg]

theorem liftB_sub_left (B0 : OspBasis F n → OspBasis F n → RModM F n r) (x x' y : RModM F n r) :
    liftB B0 (x - x') y = liftB B0 x y - liftB B0 x' y := by
  rw [sub_eq_add_neg, liftB_add_left, liftB_neg_left, ← sub_eq_add_neg]

theorem sigPow_gone (π : ZMod 2) : sigPow π (gone : GR F n r) = gone :=
  sigPow_of_even π (HasCard_gone (F := F) (n := n) (r := r)).isEven_zero

theorem VecFS2 (j k : F.K) (h : F.key j < F.key k) (w : I n) (i : F.K) :
    liftB (bracketJBasis0 JmOmega) (VBasis0 (gammaR (F := F) (n := n) (r := r)) (Fof w i))
        (VBasis0 gammaR (Sum.inr (Sum.inl ⟨(j, k), h⟩))) =
    linM (VBasis0 gammaR) (Bbeta (Fof w i) (Sum.inr (Sum.inl ⟨(j, k), h⟩))) := by
  change liftB (bracketJBasis0 JmOmega)
    (gtens gone (eN (Fof w i)) + (1 / 2 : ℚ) • ∑ l : F.K, gtens (gammaR w (F.dual l)) (Sof l i))
    (gtens gone (Sof j k)) = linM (VBasis0 gammaR) (B0data _ _ + PhiG (-GammaSF j k w i))
  simp only [liftB_add_left, liftB_rsmul_left, liftB_sum_left, liftBJ_Sof_Sof, liftBJ_eN_Sof,
    parity_Fof, sigPow_gone, gmul_gone, bracket0_Sof_Sof_gen, bracket0_Fof_Sof_gen]
  have e1 : B0data (r := r) (Fof w i : OspBasis F n) (Sum.inr (Sum.inl ⟨(j, k), h⟩)) =
      gtens gone (-bracketSF j k w i) := rfl
  have e2 : PhiG (r := r) (GammaSF j k w i : OspMod F n) =
      (1 / 2 : ℚ) • (gtens (gammaR (r := r) w k) (Sof j i) - gtens (gammaR w j) (Sof k i)) := by
    unfold GammaSF
    rw [PhiG_rsmul, PhiG_sub, PhiG_beta _ _ _ (fun W => IsQ_Sof _ _ W),
      PhiG_beta _ _ _ (fun W => IsQ_Sof _ _ W)]
  rw [e1, PhiG_neg, e2, sum_bracketSS_gtens2]
  simp only [linM_add, linM_neg, linM_rsmul, linM_sub, gtens_neg_right, linM_gtens',
    extT_bracketSF', extT_Sof _ VBasis0_SCompat, gsmul_gone_gtens, gsmul_gone, neg_sub]
  have hg : ∀ a b : F.K, F.g a b = F.g b a := F.g_symm
  simp only [V0_F, bracketSF, gtens_sub_right, gtens_rsmul_right, smul_sub, smul_add,
    Finset.smul_sum, neg_sub, hg k i, hg j i]
  have h5 : (Sof k i : OspMod F n) = -Sof i k := Sof_antisymm k i
  have h6 : (Sof j i : OspMod F n) = -Sof i j := Sof_antisymm j i
  simp only [h5, h6, gtens_neg_right, smul_neg, smul_comm (F.g i j) (1 / 2 : ℚ),
    smul_comm (F.g i k) (1 / 2 : ℚ)]
  abel

theorem sum2_g_left (cc : F.K → F.K → GR F n r) (a : F.K) (w : F.K → OspMod F n) :
    ∑ x : F.K, ∑ y : F.K, gtens (cc (F.dual x) (F.dual y)) (F.g a x • w y)
      = ∑ y : F.K, gtens (cc a (F.dual y)) (w y) := by
  simp only [gtens_rsmul_right]
  simp_rw [← Finset.smul_sum]
  rw [sum_g_right a (fun x => ∑ y : F.K, gtens (cc (F.dual x) (F.dual y)) (w y)), F.dual_dual]

theorem sum2_g_right (cc : F.K → F.K → GR F n r) (a : F.K) (w : F.K → OspMod F n) :
    ∑ x : F.K, ∑ y : F.K, gtens (cc (F.dual x) (F.dual y)) (F.g a y • w x)
      = ∑ x : F.K, gtens (cc (F.dual x) a) (w x) := by
  refine Finset.sum_congr rfl fun x _ => ?_
  exact sum_gtens_g (cc (F.dual x)) a (w x)

theorem gtens_neg_left (a : GR F n r) (v : OspMod F n) : gtens (-a) v = - gtens a v := by
  funext p; simp [gtens_apply]

theorem sum2_bracketSS (cc : F.K → F.K → GR F n r) (k l : F.K) :
    ∑ x : F.K, ∑ y : F.K, gtens (cc (F.dual x) (F.dual y)) (bracketSS k l x y : OspMod F n) =
      ∑ y : F.K, gtens (cc l (F.dual y)) (Sof k y) - ∑ y : F.K, gtens (cc k (F.dual y)) (Sof l y)
      - ∑ x : F.K, gtens (cc (F.dual x) l) (Sof k x)
      + ∑ x : F.K, gtens (cc (F.dual x) k) (Sof l x) := by
  unfold bracketSS
  simp only [gtens_add_right, gtens_sub_right, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum2_g_left cc l (fun y => Sof k y), sum2_g_left cc k (fun y => Sof l y),
    sum2_g_right cc l (fun x => Sof k x), sum2_g_right cc k (fun x => Sof l x)]

theorem sum_bracketSF_gtens (c : F.K → GR F n r) (k l : F.K) (a : I n) :
    ∑ x : F.K, gtens (c (F.dual x)) (bracketSF k l a x : OspMod F n) =
      gtens (c l) (eN (Fof a k)) - gtens (c k) (eN (Fof a l)) := by
  unfold bracketSF
  simp only [gtens_sub_right, Finset.sum_sub_distrib, sum_gtens_g]

theorem sum2_g_left' (cc : F.K → F.K → GR F n r) (a : F.K) (w : F.K → OspMod F n) :
    ∑ x : F.K, ∑ y : F.K, gtens (cc (F.dual x) (F.dual y)) (F.g x a • w y)
      = ∑ y : F.K, gtens (cc a (F.dual y)) (w y) := by
  simp_rw [F.g_symm _ a]
  exact sum2_g_left cc a w

theorem sum2_g_right' (cc : F.K → F.K → GR F n r) (a : F.K) (w : F.K → OspMod F n) :
    ∑ x : F.K, ∑ y : F.K, gtens (cc (F.dual x) (F.dual y)) (F.g y a • w x)
      = ∑ x : F.K, gtens (cc (F.dual x) a) (w x) := by
  refine Finset.sum_congr rfl fun x _ => ?_
  exact sum_gtens_g' (cc (F.dual x)) a (w x)

theorem sum2_bracketSS' (cc : F.K → F.K → GR F n r) (k l : F.K) :
    ∑ x : F.K, ∑ y : F.K, gtens (cc (F.dual x) (F.dual y)) (bracketSS x y k l : OspMod F n) =
      ∑ x : F.K, gtens (cc (F.dual x) k) (Sof x l) - ∑ y : F.K, gtens (cc k (F.dual y)) (Sof y l)
      - ∑ x : F.K, gtens (cc (F.dual x) l) (Sof x k)
      + ∑ y : F.K, gtens (cc l (F.dual y)) (Sof y k) := by
  unfold bracketSS
  simp only [gtens_add_right, gtens_sub_right, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum2_g_right' cc k (fun x => Sof x l), sum2_g_left' cc k (fun y => Sof y l),
    sum2_g_right' cc l (fun x => Sof x k), sum2_g_left' cc l (fun y => Sof y k)]

theorem V0_L (u v : I n) (h : Bmn.IKey u ≤ Bmn.IKey v) :
    VBasis0 (gammaR (F := F) (n := n) (r := r)) (Sum.inl ⟨(u, v), h⟩) =
      gtens gone (eN (Lof u v)) + ∑ i : F.K, (gtens (gammaR v (F.dual i)) (eN (Fof u i)) +
        gtens (gammaR u (F.dual i)) (eN (Fof v i))) -
      (1 / 2 : ℚ) • ∑ i : F.K, ∑ j : F.K,
        gtens (gmul (gammaR u (F.dual i)) (gammaR v (F.dual j))) (Sof i j) := rfl

theorem VecSL2 (k l : F.K) (h : F.key k < F.key l) (u v : I n) (h1 : Bmn.IKey u ≤ Bmn.IKey v) :
    liftB (bracketJBasis0 JmOmega) (VBasis0 (gammaR (F := F) (n := n) (r := r))
        (Sum.inr (Sum.inl ⟨(k, l), h⟩))) (VBasis0 gammaR (Sum.inl ⟨(u, v), h1⟩)) =
    linM (VBasis0 gammaR) (Bbeta (Sum.inr (Sum.inl ⟨(k, l), h⟩)) (Sum.inl ⟨(u, v), h1⟩)) := by
  change liftB (bracketJBasis0 JmOmega) (gtens gone (Sof k l)) _ =
    linM (VBasis0 gammaR) (B0data _ _ + PhiG (-GammaLS u v k l))
  rw [V0_L]
  simp only [liftB_sub_right, liftB_add_right, liftB_rsmul_right, liftB_sum_right, liftBJ_Sof_eN,
    liftBJ_Sof_Sof, gone_gmul, bracket0_Sof_Fof_gen, bracket0_Sof_Sof_gen, bracket0_Sof_Lof]
  have e1 : B0data (r := r) (Sum.inr (Sum.inl ⟨(k, l), h⟩) : OspBasis F n) (Sum.inl ⟨(u, v), h1⟩)
      = 0 := by unfold B0data; simp [bracket0Basis, gtens_zero_right]
  have e2 : PhiG (r := r) (-GammaLS u v k l : OspMod F n) =
      -(gtens (gammaR u k) (eN (Fof v l)) - gtens (gammaR u l) (eN (Fof v k)) +
        gtens (gammaR v k) (eN (Fof u l)) - gtens (gammaR v l) (eN (Fof u k))) := by
    unfold GammaLS
    rw [PhiG_neg, PhiG_sub, PhiG_add, PhiG_sub]
    simp only [PhiG_beta _ _ _ (fun W => IsQ_eN _ W)]
  rw [e1, e2, sum2_bracketSS (fun a b => gmul (gammaR u a) (gammaR v b)) k l]
  simp only [linM_add, linM_neg, linM_sub, zero_add, linM_gtens_eN, V0_F, gsmul_add_right,
    gsmul_rsmul_right, gsmul_sum_right, gsmul_gtens, gtens_zero_right, zero_add]
  have h3 : ∀ y : F.K, (Sof k y : OspMod F n) = -Sof y k := fun y => Sof_antisymm k y
  have h4 : ∀ y : F.K, (Sof l y : OspMod F n) = -Sof y l := fun y => Sof_antisymm l y
  have h5 : ∀ x : F.K, gmul (gammaR (F := F) (n := n) (r := r) u (F.dual x)) (gammaR v l) =
      - gmul (gammaR v l) (gammaR u (F.dual x)) := fun x => gammaR_anticomm u v _ _
  have h6 : ∀ x : F.K, gmul (gammaR (F := F) (n := n) (r := r) u (F.dual x)) (gammaR v k) =
      - gmul (gammaR v k) (gammaR u (F.dual x)) := fun x => gammaR_anticomm u v _ _
  simp only [Finset.sum_add_distrib, sum_bracketSF_gtens, gmul_gone, h3, h4, h5, h6,
    gtens_neg_right, gtens_neg_left, Finset.sum_neg_distrib, smul_add, smul_sub, smul_neg]
  abel

theorem VecLS2 (u v : I n) (h1 : Bmn.IKey u ≤ Bmn.IKey v) (k l : F.K) (h : F.key k < F.key l) :
    liftB (bracketJBasis0 JmOmega) (VBasis0 (gammaR (F := F) (n := n) (r := r))
        (Sum.inl ⟨(u, v), h1⟩)) (VBasis0 gammaR (Sum.inr (Sum.inl ⟨(k, l), h⟩))) =
    linM (VBasis0 gammaR) (Bbeta (Sum.inl ⟨(u, v), h1⟩) (Sum.inr (Sum.inl ⟨(k, l), h⟩))) := by
  change liftB (bracketJBasis0 JmOmega) _ (gtens gone (Sof k l)) =
    linM (VBasis0 gammaR) (B0data _ _ + PhiG (GammaLS u v k l))
  rw [V0_L]
  simp only [liftB_sub_left, liftB_add_left, liftB_rsmul_left, liftB_sum_left, liftBJ_eN_Sof,
    liftBJ_Sof_Sof, gmul_gone, bracket0_Fof_Sof_gen, bracket0_Sof_Sof_gen, bracket0_Lof_Sof,
    parity_Fof, parity_Lof, sigPow_gone]
  have e1 : B0data (r := r) (Sum.inl ⟨(u, v), h1⟩ : OspBasis F n) (Sum.inr (Sum.inl ⟨(k, l), h⟩))
      = 0 := by unfold B0data; simp [bracket0Basis, gtens_zero_right]
  have e2 : PhiG (r := r) (GammaLS u v k l : OspMod F n) =
      (gtens (gammaR u k) (eN (Fof v l)) - gtens (gammaR u l) (eN (Fof v k)) +
        gtens (gammaR v k) (eN (Fof u l)) - gtens (gammaR v l) (eN (Fof u k))) := by
    unfold GammaLS
    rw [PhiG_sub, PhiG_add, PhiG_sub]
    simp only [PhiG_beta _ _ _ (fun W => IsQ_eN _ W)]
  rw [e1, e2, sum2_bracketSS' (fun a b => gmul (gammaR u a) (gammaR v b)) k l]
  simp only [linM_add, linM_sub, zero_add, linM_gtens_eN, V0_F, gsmul_add_right,
    gsmul_rsmul_right, gsmul_sum_right, gsmul_gtens, gtens_zero_right, zero_add]
  have h5 : ∀ x : F.K, gmul (gammaR (F := F) (n := n) (r := r) u (F.dual x)) (gammaR v l) =
      - gmul (gammaR v l) (gammaR u (F.dual x)) := fun x => gammaR_anticomm u v _ _
  have h6 : ∀ x : F.K, gmul (gammaR (F := F) (n := n) (r := r) u (F.dual x)) (gammaR v k) =
      - gmul (gammaR v k) (gammaR u (F.dual x)) := fun x => gammaR_anticomm u v _ _
  simp only [gtens_neg_right, Finset.sum_add_distrib, Finset.sum_neg_distrib, sum_bracketSF_gtens,
    gmul_gone, h5, h6, gtens_neg_left, smul_add, smul_sub, smul_neg]
  abel

theorem sigPow_one_gammaR (u : I n) (i : F.K) :
    sigPow 1 (gammaR (F := F) (n := n) (r := r) u i) = - gammaR u i := by
  have h1 : (1 : ZMod 2) ≠ 0 := by decide
  unfold sigPow
  rw [ite_eq_right h1]
  exact GRing.sig_of_odd (by simpa using (HasCard_gammaR (F := F) (n := n) (r := r) u i).parity)

theorem gtens_JR (u v : I n) (w : OspMod F n) :
    gtens (JR (F := F) (r := r) u v) w = (J n u v) • gtens gone w := by
  funext p
  by_cases h : p.2 = ∅
  · simp [gtens_apply, JR, gone, h, MvPolynomial.smul_eq_C_mul]
  · simp [gtens_apply, JR, gone, h]

theorem gtens_JmOmega (u v : I n) (w : OspMod F n) :
    gtens (JmOmega (F := F) (r := r) u v) w = (J n u v) • gtens gone w - gtens (OmegaR u v) w := by
  unfold JmOmega
  funext p
  simp only [gtens_apply, JR, gone, Pi.sub_apply, Pi.smul_apply, sub_mul]
  by_cases h : p.2 = ∅
  · simp [h, MvPolynomial.smul_eq_C_mul]
  · simp [h]

theorem sum_gmul_gammaR_dual (u v : I n) :
    ∑ k : F.K, gmul (gammaR (F := F) (n := n) (r := r) u (F.dual k)) (gammaR v k)
      = - OmegaR u v := by
  unfold OmegaR
  rw [neg_neg, ← Equiv.sum_comp (Function.Involutive.toPerm F.dual F.dual_dual)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [F.dual_dual]

theorem sum2_bracketSS'' (cc : F.K → F.K → GR F n r) (i j : F.K) :
    ∑ k : F.K, ∑ l : F.K, gtens (cc (F.dual k) (F.dual l)) (bracketSS k i l j : OspMod F n) =
      ∑ k : F.K, gtens (cc (F.dual k) i) (Sof k j) - ∑ k : F.K, gtens (cc (F.dual k) k) (Sof i j)
      - F.g i j • ∑ k : F.K, ∑ l : F.K, gtens (cc (F.dual k) (F.dual l)) (Sof k l)
      + ∑ l : F.K, gtens (cc j (F.dual l)) (Sof i l) := by
  unfold bracketSS
  simp only [gtens_add_right, gtens_sub_right, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum2_g_right cc i (fun x => Sof x j), sum2_g_left' cc j (fun y => Sof i y)]
  have e2 : ∑ x : F.K, ∑ y : F.K,
      gtens (cc (F.dual x) (F.dual y)) (F.g x y • (Sof i j : OspMod F n))
      = ∑ x : F.K, gtens (cc (F.dual x) x) (Sof i j) :=
    Finset.sum_congr rfl fun x _ => sum_gtens_g (cc (F.dual x)) x (Sof i j)
  rw [e2]
  simp only [gtens_rsmul_right, Finset.smul_sum]

theorem V0_Lof (u v : I n) :
    VBasis0 (gammaR (F := F) (n := n) (r := r)) (Lof u v) =
      gtens gone (eN (Lof u v)) + ∑ i : F.K, (gtens (gammaR v (F.dual i)) (eN (Fof u i)) +
        gtens (gammaR u (F.dual i)) (eN (Fof v i))) -
      (1 / 2 : ℚ) • ∑ i : F.K, ∑ j : F.K,
        gtens (gmul (gammaR u (F.dual i)) (gammaR v (F.dual j))) (Sof i j) := by
  by_cases h : Bmn.IKey u ≤ Bmn.IKey v
  · have e : (Lof u v : OspBasis F n) = Sum.inl ⟨(u, v), h⟩ := Lof_of_le h
    conv_lhs => rw [e]
    exact V0_L u v h
  · have e : (Lof u v : OspBasis F n) = Sum.inl ⟨(v, u), (Nat.not_le.mp h).le⟩ := by
      unfold Lof; exact dite_eq_right h
    conv_lhs => rw [e]
    rw [V0_L v u (Nat.not_le.mp h).le, Lof_comm v u]
    refine congrArg₂ (· - ·) (congrArg₂ (· + ·) rfl
      (Finset.sum_congr rfl fun i _ => add_comm _ _)) (congrArg (fun q => (1 / 2 : ℚ) • q) ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [gammaR_anticomm v u (F.dual j) (F.dual i), gtens_neg_left, Sof_antisymm j i,
      gtens_neg_right, neg_neg]

theorem sum_bracketSF_gtens' (c : F.K → GR F n r) (i j : F.K) (a : I n) :
    ∑ x : F.K, gtens (c (F.dual x)) (bracketSF x i a j : OspMod F n) =
      F.g i j • ∑ x : F.K, gtens (c (F.dual x)) (eN (Fof a x)) - gtens (c j) (eN (Fof a i)) := by
  unfold bracketSF
  simp only [gtens_sub_right, Finset.sum_sub_distrib]
  rw [sum_gtens_g' c j (eN (Fof a i))]
  simp only [gtens_rsmul_right, Finset.smul_sum]

theorem VecFF2 (u v : I n) (i j : F.K) :
    liftB (bracketJBasis0 JmOmega) (VBasis0 (gammaR (F := F) (n := n) (r := r)) (Fof u i))
        (VBasis0 gammaR (Fof v j)) =
    linM (VBasis0 gammaR) (Bbeta (Fof u i) (Fof v j)) := by
  rw [V0_F, V0_F]
  have e1 : Bbeta (r := r) (Fof u i : OspBasis F n) (Fof v j) =
      gtens gone (bracketFF u i v j) + PhiG (GammaFF u i v j) := by
    rw [Bbeta_eq_PhiG]; rfl
  have e2 : PhiG (r := r) (GammaFF u i v j : OspMod F n) =
      -(1 / 2 : ℚ) • (gtens (gammaR u j) (eN (Fof v i)) + gtens (gammaR v i) (eN (Fof u j))) := by
    unfold GammaFF
    rw [PhiG_rsmul, PhiG_add, PhiG_beta _ _ _ (fun W => IsQ_eN _ W),
      PhiG_beta _ _ _ (fun W => IsQ_eN _ W)]
  rw [e1, e2]
  simp only [liftB_add_left, liftB_add_right, liftB_rsmul_left, liftB_rsmul_right,
    liftB_sum_left, liftB_sum_right, liftBJ_eN_eN, liftBJ_eN_Sof, liftBJ_Sof_eN, liftBJ_Sof_Sof,
    parity_Fof, sigPow_gone, sigPow_one_gammaR, gone_gmul, gmul_gone, bracket0_Fof_Sof_gen,
    bracket0_Sof_Fof_gen, bracket0_Sof_Sof_gen]
  have hP4 : ∑ x : F.K, ∑ x1 : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) u (F.dual x1))
      (gammaR v (F.dual x))) (bracketSS x1 i x j : OspMod F n) =
      ∑ k : F.K, gtens (gmul (gammaR u (F.dual k)) (gammaR v i)) (Sof k j) -
        gtens (∑ k : F.K, gmul (gammaR u (F.dual k)) (gammaR v k)) (Sof i j) -
        F.g i j • ∑ k : F.K, ∑ l : F.K,
          gtens (gmul (gammaR u (F.dual k)) (gammaR v (F.dual l))) (Sof k l) +
        ∑ l : F.K, gtens (gmul (gammaR u j) (gammaR v (F.dual l))) (Sof i l) := by
    rw [Finset.sum_comm,
      sum2_bracketSS'' (fun a b => gmul (gammaR u a) (gammaR v b)) i j, gtens_sum_left]
  rw [bracketJBasis0_F_F, gsmul_gone, gtens_JmOmega]
  simp only [gtens_neg_left, gtens_neg_right, neg_neg, smul_add, Finset.sum_add_distrib,
    sum_bracketSF_gtens', Finset.smul_sum]
  have hP4' : ∑ x : F.K, ∑ x1 : F.K, (1 / 2 : ℚ) • (1 / 2 : ℚ) •
      gtens (gmul (gammaR (F := F) (n := n) (r := r) u (F.dual x1)) (gammaR v (F.dual x)))
        (bracketSS x1 i x j : OspMod F n) = (1 / 4 : ℚ) • ∑ x : F.K, ∑ x1 : F.K,
        gtens (gmul (gammaR u (F.dual x1)) (gammaR v (F.dual x))) (bracketSS x1 i x j) := by
    simp only [Finset.smul_sum, smul_smul]
    norm_num
  rw [hP4', hP4, sum_gmul_gammaR_dual, bracketFF]
  simp only [gtens_add_right, gtens_rsmul_right, linM_add, linM_rsmul, linM_gtens', extT_Sof _
    VBasis0_SCompat, gsmul_gone, gtens_neg_left, extT_eN, V0_Lof, V0_F, gsmul_add_right,
    gsmul_rsmul_right, gsmul_sum_right, gsmul_gtens, gone_gmul]
  have h5 : ∀ x : F.K, gmul (gammaR (F := F) (n := n) (r := r) u (F.dual x)) (gammaR v i) =
      - gmul (gammaR v i) (gammaR u (F.dual x)) := fun x => gammaR_anticomm u v _ _
  have h6 : ∀ l : F.K, (Sof i l : OspMod F n) = -Sof l i := fun l => Sof_antisymm i l
  have hg : F.g j i = F.g i j := F.g_symm j i
  simp only [h5, h6, hg, gtens_neg_left, gtens_neg_right, Finset.sum_neg_distrib, smul_add,
    smul_sub, smul_neg, Finset.smul_sum, Finset.sum_add_distrib]
  simp only [gmul_gone, smul_smul, ← Finset.smul_sum]
  module

theorem sum2_bracketSF (cc : F.K → F.K → GR F n r) (w : I n) (i : F.K) :
    ∑ x : F.K, ∑ y : F.K, gtens (cc (F.dual x) (F.dual y)) (bracketSF x y w i : OspMod F n) =
      ∑ x : F.K, gtens (cc (F.dual x) i) (eN (Fof w x)) -
        ∑ y : F.K, gtens (cc i (F.dual y)) (eN (Fof w y)) := by
  unfold bracketSF
  simp only [gtens_sub_right, Finset.sum_sub_distrib]
  rw [sum2_g_right' cc i (fun x => eN (Fof w x)), sum2_g_left' cc i (fun y => eN (Fof w y))]

theorem sum2_bracketSF_snd (cc : F.K → F.K → GR F n r) (a : I n) (i : F.K) :
    ∑ x : F.K, ∑ x1 : F.K, gtens (cc (F.dual x1) (F.dual x)) (bracketSF x i a x1 : OspMod F n) =
      ∑ x : F.K, gtens (cc i (F.dual x)) (eN (Fof a x)) -
        gtens (∑ x : F.K, cc x (F.dual x)) (eN (Fof a i)) := by
  unfold bracketSF
  simp only [gtens_sub_right, Finset.sum_sub_distrib]
  rw [gtens_sum_left]
  refine congrArg₂ (· - ·) ?_ ?_
  · exact Finset.sum_congr rfl fun x _ => sum_gtens_g (fun a' => cc a' (F.dual x)) i (eN (Fof a x))
  · refine Finset.sum_congr rfl fun x _ => ?_
    exact sum_gtens_g (fun a' => cc a' (F.dual x)) x (eN (Fof a i))

theorem bracket0_Sof_Lof_inl (k l : F.K) (v w : I n) (h : Bmn.IKey v ≤ Bmn.IKey w) :
    bracket0 (Sof k l : OspMod F n) (eN (Sum.inl ⟨(v, w), h⟩ : OspBasis F n)) = 0 := by
  have := bracket0_Sof_Lof (F := F) (n := n) k l v w
  rwa [Lof_of_le h] at this

theorem parity_inl (p : {q : I n × I n // Bmn.IKey q.1 ≤ Bmn.IKey q.2}) :
    parity (Sum.inl p : OspBasis F n) = 0 := rfl

theorem gmul_sub_right' (a b c : GR F n r) : gmul a (b - c) = gmul a b - gmul a c := by
  rw [sub_eq_add_neg, gmul_add_right, gmul_neg_right, ← sub_eq_add_neg]

theorem gsmul_neg_left (a : GR F n r) (w : RModM F n r) : gsmul (-a) w = - gsmul a w := by
  funext p
  have e : gsmul (-a) w p = gmul (-a) (grComp w p.1) p.2 := rfl
  rw [e, gmul_neg_left]; rfl

theorem gsmul_sub_right (a : GR F n r) (w w' : RModM F n r) :
    gsmul a (w - w') = gsmul a w - gsmul a w' := by
  rw [sub_eq_add_neg, gsmul_add_right, gsmul_neg_right, ← sub_eq_add_neg]

theorem Bbeta_FL (u : I n) (i : F.K) (v w : I n) (h : Bmn.IKey v ≤ Bmn.IKey w) :
    Bbeta (r := r) (Fof u i : OspBasis F n) (Sum.inl ⟨(v, w), h⟩) =
      - Bbeta (Sum.inl ⟨(v, w), h⟩) (Fof u i) := by
  have e1 : B0data (r := r) (Fof u i : OspBasis F n) (Sum.inl ⟨(v, w), h⟩) =
      - B0data (Sum.inl ⟨(v, w), h⟩) (Fof u i) := by
    unfold B0data
    rw [← gtens_neg_right]; rfl
  have e2 : GammaBasis (Fof u i : OspBasis F n) (Sum.inl ⟨(v, w), h⟩) =
      - GammaBasis (Sum.inl ⟨(v, w), h⟩) (Fof u i) := by
    change -GammaLF v w u i = _
    rw [neg_inj]; rfl
  rw [Bbeta_eq_PhiG, Bbeta_eq_PhiG, e1, e2, PhiG_neg, neg_add]

theorem sum_gtens_Omega (u w : I n) (v : OspMod F n) :
    ∑ x : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) u (F.dual x)) (gammaR w x)) v =
      - gtens (OmegaR u w) v := by
  rw [← gtens_sum_left, sum_gmul_gammaR_dual, gtens_neg_left]

theorem sum_gtens_Omega' (u w : I n) (v : OspMod F n) :
    ∑ x : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) u x) (gammaR w (F.dual x))) v =
      - gtens (OmegaR u w) v := by
  rw [← gtens_sum_left]
  unfold OmegaR
  rw [gtens_neg_left, neg_neg]

theorem eq_dual_iff (i x : F.K) : i = F.dual x ↔ x = F.dual i := by
  constructor <;> intro h <;> rw [h, F.dual_dual]

theorem sum_ite_dual_a {M : Type*} [AddCommMonoid M] (f : F.K → F.K → M) :
    ∑ x : F.K, ∑ y : F.K, (if x = F.dual y then f x y else 0) = ∑ y : F.K, f (F.dual y) y := by
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq']

theorem sum_ite_dual_b {M : Type*} [AddCommMonoid M] (f : F.K → F.K → F.K → M) :
    ∑ x : F.K, ∑ y : F.K, ∑ z : F.K, (if x = F.dual z then f x y z else 0) =
      ∑ y : F.K, ∑ z : F.K, f (F.dual z) y z := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq']

theorem gammaR_odd (u : I n) (i : F.K) :
    HasParity (1 : ZMod 2) (gammaR (F := F) (n := n) (r := r) u i) := by
  simpa using (HasCard_gammaR (F := F) (n := n) (r := r) u i).parity

theorem tri_cyc {a b c : GR F n r} (ha : HasParity 1 a) (hb : HasParity 1 b)
    (hc : HasParity 1 c) : gmul a (gmul b c) = gmul b (gmul c a) := by
  have h1 := GRing.mul_anticomm_of_odd (a := GRing.ofGR a) (b := GRing.ofGR b) ha hb
  have h2 := GRing.mul_anticomm_of_odd (a := GRing.ofGR a) (b := GRing.ofGR c) ha hc
  have h3 : GRing.ofGR a * (GRing.ofGR b * GRing.ofGR c) =
      GRing.ofGR b * (GRing.ofGR c * GRing.ofGR a) := by
    rw [← mul_assoc, h1, neg_mul, mul_assoc, h2, mul_neg, neg_neg]
  exact h3

theorem tri_rev {a b c : GR F n r} (ha : HasParity 1 a) (hb : HasParity 1 b)
    (hc : HasParity 1 c) : gmul a (gmul b c) = - gmul c (gmul b a) := by
  have h1 := GRing.mul_anticomm_of_odd (a := GRing.ofGR b) (b := GRing.ofGR c) hb hc
  have h2 := GRing.mul_anticomm_of_odd (a := GRing.ofGR a) (b := GRing.ofGR c) ha hc
  have h3 := GRing.mul_anticomm_of_odd (a := GRing.ofGR a) (b := GRing.ofGR b) ha hb
  have h4 : GRing.ofGR a * (GRing.ofGR b * GRing.ofGR c) =
      - (GRing.ofGR c * (GRing.ofGR b * GRing.ofGR a)) := by
    rw [h1, mul_neg, ← mul_assoc, h2, neg_mul, mul_assoc, h3, mul_neg, neg_neg]
  exact h4

theorem sum_gtens_tri_Omega (u v : I n) (c : GR F n r) (V : OspMod F n) :
    ∑ x : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) u x)
        (gmul (gammaR v (F.dual x)) c)) V = - gtens (gmul (OmegaR u v) c) V := by
  simp_rw [← gmul_assoc]
  rw [← gtens_sum_left, ← gmul_sum_left]
  unfold OmegaR
  rw [gmul_neg_left, gtens_neg_left, neg_neg]

theorem sum_gtens_tri_Omega' (u v : I n) (c : GR F n r) (V : OspMod F n) :
    ∑ x : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) u (F.dual x))
        (gmul (gammaR v x) c)) V = - gtens (gmul (OmegaR u v) c) V := by
  simp_rw [← gmul_assoc]
  rw [← gtens_sum_left, ← gmul_sum_left, sum_gmul_gammaR_dual, gmul_neg_left, gtens_neg_left]

theorem gtens_ite (a : GR F n r) (p : Prop) [Decidable p] (v : OspMod F n) :
    gtens a (if p then v else 0) = if p then gtens a v else 0 := by
  split_ifs <;> simp [gtens_zero_right]

-- one large `simp` normalizes both sides; the closing `module` needs its result
theorem VecFL2 (u : I n) (i : F.K) (v w : I n) (h1 : Bmn.IKey v ≤ Bmn.IKey w) :
    liftB (bracketJBasis0 JmOmega) (VBasis0 (gammaR (F := F) (n := n) (r := r)) (Fof u i))
        (VBasis0 gammaR (Sum.inl ⟨(v, w), h1⟩)) =
    linM (VBasis0 gammaR) (Bbeta (Fof u i) (Sum.inl ⟨(v, w), h1⟩)) := by
  have hLof : (Lof v w : OspBasis F n) = Sum.inl ⟨(v, w), h1⟩ := Lof_of_le h1
  rw [V0_F, V0_L, hLof]
  simp only [liftB_sub_right, liftB_add_left, liftB_add_right, liftB_rsmul_left,
    liftB_rsmul_right, liftB_sum_left, liftB_sum_right, liftBJ_eN_eN, liftBJ_eN_Sof,
    liftBJ_Sof_eN, liftBJ_Sof_Sof, parity_Fof, sigPow_gone, sigPow_one_gammaR,
    gone_gmul, gmul_gone, bracket0_Fof_Sof_gen, bracket0_Sof_Fof_gen, bracket0_Sof_Sof_gen,
    bracket0_Sof_Lof_inl, sigPow_gmul, gmul_neg_left, gmul_neg_right, neg_neg]
  rw [bracketJBasis0_F_L]
  simp only [bracketJBasis0_F_F, gsmul_gone, gsmul_add_right, gsmul_rsmul_right, gsmul_gtens,
    gtens_zero_right, Finset.sum_const_zero, smul_zero, gsmul_sub_right,
    gtens_JmOmega]
  rw [Bbeta_FL]
  have e1 : B0data (r := r) (Sum.inl ⟨(v, w), h1⟩ : OspBasis F n) (Fof u i) =
      gtens gone (bracketLF v w u i) := rfl
  have e2 : PhiG (r := r) (GammaLF v w u i : OspMod F n) =
      (1 / 2 : ℚ) • (gtens (gammaR v i) (eN (Lof w u)) + gtens (gammaR w i) (eN (Lof v u))) := by
    unfold GammaLF
    rw [PhiG_rsmul, PhiG_add, PhiG_beta _ _ _ (fun W => IsQ_eN _ W),
      PhiG_beta _ _ _ (fun W => IsQ_eN _ W)]
  have eG : (GammaBasis (Sum.inl ⟨(v, w), h1⟩ : OspBasis F n) (Fof u i) : OspMod F n) =
      GammaLF v w u i := rfl
  rw [Bbeta_eq_PhiG, e1, eG, e2]
  simp only [linM_neg, linM_add, linM_rsmul, linM_gtens', extT_eN, V0_F, V0_Lof, bracketLF,
    gtens_add_right, gtens_rsmul_right, gsmul_add_right, gsmul_rsmul_right, gsmul_sum_right,
    gsmul_gtens, gsmul_sub_right, gone_gmul, gmul_gone]
  simp only [bracketSF, bracketSS, FermionIndex.g, mul_ite, mul_one, mul_zero, ite_smul, one_smul,
    zero_smul, gtens_ite, gtens_add_right, gtens_sub_right,
    smul_add, smul_sub, smul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, Finset.smul_sum, gtens_neg_left, gmul_neg_left,
    neg_sub]
  simp only [one_div, neg_add_rev, neg_sub, add_zero, sub_neg_eq_add, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, F.dual_dual, smul_ite, smul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, eq_dual_iff]
  have hJ1 : J n v u = -J n u v := Bmn.J_antisymm v u
  have hJ2 : J n w u = -J n u w := Bmn.J_antisymm w u
  have hO1 : OmegaR (F := F) (r := r) v u = -OmegaR u v := OmegaR_antisymm u v
  have hO2 : OmegaR (F := F) (r := r) w u = -OmegaR u w := OmegaR_antisymm u w
  have hL1 : (Lof w u : OspBasis F n) = Lof u w := Lof_comm w u
  have hL2 : (Lof v u : OspBasis F n) = Lof u v := Lof_comm v u
  have hSx : ∀ x : F.K, (Sof x i : OspMod F n) = -Sof i x := fun x => Sof_antisymm x i
  have hOc : ∀ (a : GR F n r) (p q : I n), gmul a (OmegaR (F := F) (r := r) p q) =
      gmul (OmegaR p q) a := fun a p q =>
    (gmul_comm_of_even ((HasCard_OmegaR (F := F) (r := r) p q).isEven (by norm_num)) a).symm
  have hT1 : ∀ p q : F.K, gmul (gammaR (F := F) (n := n) (r := r) u p)
      (gmul (gammaR v i) (gammaR w q)) = gmul (gammaR v i) (gmul (gammaR w q) (gammaR u p)) :=
    fun p q => tri_cyc (gammaR_odd _ _) (gammaR_odd _ _) (gammaR_odd _ _)
  have hT3 : ∀ p q : F.K, gmul (gammaR (F := F) (n := n) (r := r) u p)
      (gmul (gammaR v q) (gammaR w i)) = - gmul (gammaR w i) (gmul (gammaR v q) (gammaR u p)) :=
    fun p q => tri_rev (gammaR_odd _ _) (gammaR_odd _ _) (gammaR_odd _ _)
  have hA1 : ∀ p : F.K, gmul (gammaR (F := F) (n := n) (r := r) u p) (gammaR w i) =
      - gmul (gammaR w i) (gammaR u p) := fun p => gammaR_anticomm _ _ _ _
  have hA2 : ∀ p : F.K, gmul (gammaR (F := F) (n := n) (r := r) u p) (gammaR v i) =
      - gmul (gammaR v i) (gammaR u p) := fun p => gammaR_anticomm _ _ _ _
  have hA3 : ∀ p : F.K, gmul (gammaR (F := F) (n := n) (r := r) v p) (gammaR w i) =
      - gmul (gammaR w i) (gammaR v p) := fun p => gammaR_anticomm _ _ _ _
  have hT3' : ∀ p q : F.K, gmul (gammaR (F := F) (n := n) (r := r) u p)
      (gmul (gammaR w i) (gammaR v q)) = gmul (gammaR w i) (gmul (gammaR v q) (gammaR u p)) :=
    fun p q => tri_cyc (gammaR_odd _ _) (gammaR_odd _ _) (gammaR_odd _ _)
  have hT4 : ∀ p q r' : F.K, gmul (gammaR (F := F) (n := n) (r := r) u p)
      (gmul (gammaR v q) (gammaR w r')) = - gmul (gammaR u p) (gmul (gammaR w r') (gammaR v q)) :=
    fun p q r' => by rw [gammaR_anticomm v w q r', gmul_neg_right]
  have hT2 : ∑ x : F.K, ∑ x1 : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) u x)
      (gmul (gammaR v (F.dual x)) (gammaR w (F.dual x1)))) (Sof i x1 : OspMod F n) =
      - ∑ x1 : F.K, gtens (gmul (OmegaR u v) (gammaR w (F.dual x1))) (Sof i x1) := by
    rw [Finset.sum_comm]
    simp only [sum_gtens_tri_Omega, Finset.sum_neg_distrib]
  have hS1 : ∑ x : F.K, ∑ x1 : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) v i)
      (gmul (gammaR w (F.dual x)) (gammaR u (F.dual x1)))) (Sof x1 x : OspMod F n) =
      - ∑ x : F.K, ∑ x1 : F.K, gtens (gmul (gammaR v i)
      (gmul (gammaR w (F.dual x)) (gammaR u (F.dual x1)))) (Sof x x1) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x1 _ => ?_
    rw [Sof_antisymm x1 x, gtens_neg_right]
  have hS3 : ∑ x : F.K, ∑ x1 : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) w i)
      (gmul (gammaR v (F.dual x)) (gammaR u (F.dual x1)))) (Sof x1 x : OspMod F n) =
      - ∑ x : F.K, ∑ x1 : F.K, gtens (gmul (gammaR w i)
      (gmul (gammaR v (F.dual x)) (gammaR u (F.dual x1)))) (Sof x x1) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x1 _ => ?_
    rw [Sof_antisymm x1 x, gtens_neg_right]
  simp only [← Finset.smul_sum]
  rw [hT2]
  simp only [hJ1, hJ2, hO1, hO2, hL1, hL2, hSx, hOc, hT1, hT3', hT4, hA1, hA2, hA3,
    gmul_neg_right, gtens_neg_left, gtens_neg_right, smul_neg, neg_smul,
    Finset.sum_neg_distrib, neg_neg, sum_gtens_tri_Omega, sum_gtens_Omega']
  rw [hS1, hS3]
  module

theorem gtens_sub_left (a b : GR F n r) (v : OspMod F n) :
    gtens (a - b) v = gtens a v - gtens b v := by
  funext p; simp [gtens_apply, sub_mul]

theorem sum_gtens_pair_Omega' (v w : I n) (a : GR F n r) (V : OspMod F n) :
    ∑ x : F.K, gtens (gmul a (gmul (gammaR (F := F) (n := n) (r := r) v x)
        (gammaR w (F.dual x)))) V = - gtens (gmul a (OmegaR v w)) V := by
  have h : ∑ x : F.K, gmul (gammaR (F := F) (n := n) (r := r) v x) (gammaR w (F.dual x))
      = - OmegaR v w := by
    unfold OmegaR; rw [neg_neg]
  rw [← gtens_sum_left, ← gmul_sum_right, h, gmul_neg_right, gtens_neg_left]

theorem tri_swap12_gamma {u v w : I n} {a b c : F.K} :
    gmul (gammaR (F := F) (n := n) (r := r) u a) (gmul (gammaR v b) (gammaR w c)) =
      - gmul (gammaR v b) (gmul (gammaR u a) (gammaR w c)) := by
  rw [← gmul_assoc, gammaR_anticomm u v, gmul_neg_left, gmul_assoc]

theorem sum_gtens_pre_tri_Omega (a : GR F n r) (v w : I n) (c : GR F n r) (V : OspMod F n) :
    ∑ x : F.K, gtens (gmul a (gmul (gammaR (F := F) (n := n) (r := r) v x)
        (gmul (gammaR w (F.dual x)) c))) V = - gtens (gmul a (gmul (OmegaR v w) c)) V := by
  have h : ∑ x : F.K, gmul (gammaR (F := F) (n := n) (r := r) v x) (gammaR w (F.dual x))
      = - OmegaR v w := by
    unfold OmegaR; rw [neg_neg]
  have h2 : ∑ x : F.K, gmul (gammaR (F := F) (n := n) (r := r) v x)
      (gmul (gammaR w (F.dual x)) c) = gmul (- OmegaR v w) c := by
    rw [← h, gmul_sum_left]
    simp only [gmul_assoc]
  rw [← gtens_sum_left, ← gmul_sum_right, h2, gmul_neg_left, gmul_neg_right, gtens_neg_left]


/-! ### Contractions of `γ`-products (used in `VecLL2`) -/

theorem gmul_swap12_gamma {p q : I n} {a b : F.K} (c : GR F n r) :
    gmul (gammaR (F := F) (n := n) (r := r) p a) (gmul (gammaR q b) c) =
      - gmul (gammaR q b) (gmul (gammaR p a) c) := by
  rw [← gmul_assoc, gammaR_anticomm p q, gmul_neg_left, gmul_assoc]

theorem cubA (p q a f : I n) :
    ∑ x : F.K, ∑ x1 : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) p (F.dual x1))
      (gmul (gammaR q x) (gammaR a (F.dual x)))) (eN (Fof f x1) : OspMod F n) =
    - ∑ x1 : F.K, gtens (gmul (gammaR p (F.dual x1)) (OmegaR q a)) (eN (Fof f x1)) := by
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun x1 _ => sum_gtens_pair_Omega' q a _ _

theorem cubB (p q a f : I n) :
    ∑ x : F.K, ∑ x1 : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) p x)
      (gmul (gammaR q (F.dual x1)) (gammaR a (F.dual x)))) (eN (Fof f x1) : OspMod F n) =
    ∑ x1 : F.K, gtens (gmul (OmegaR p a) (gammaR q (F.dual x1))) (eN (Fof f x1)) := by
  have e : ∀ x x1 : F.K, gmul (gammaR (F := F) (n := n) (r := r) p x)
      (gmul (gammaR q (F.dual x1)) (gammaR a (F.dual x))) =
      - gmul (gammaR p x) (gmul (gammaR a (F.dual x)) (gammaR q (F.dual x1))) :=
    fun x x1 => by rw [gammaR_anticomm q a, gmul_neg_right]
  simp only [e, gtens_neg_left, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  simp only [sum_gtens_tri_Omega, Finset.sum_neg_distrib, neg_neg]

theorem cubC (q a b f : I n) :
    ∑ x : F.K, ∑ x1 : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) q x)
      (gmul (gammaR a (F.dual x)) (gammaR b (F.dual x1)))) (eN (Fof f x1) : OspMod F n) =
    - ∑ x1 : F.K, gtens (gmul (OmegaR q a) (gammaR b (F.dual x1))) (eN (Fof f x1)) := by
  rw [Finset.sum_comm]
  simp only [sum_gtens_tri_Omega, Finset.sum_neg_distrib]

theorem cubD (q a b f : I n) :
    ∑ x : F.K, ∑ x1 : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) q x1)
      (gmul (gammaR a (F.dual x)) (gammaR b (F.dual x1)))) (eN (Fof f x) : OspMod F n) =
    ∑ x : F.K, gtens (gmul (OmegaR q b) (gammaR a (F.dual x))) (eN (Fof f x)) := by
  have e : ∀ x x1 : F.K, gmul (gammaR (F := F) (n := n) (r := r) q x1)
      (gmul (gammaR a (F.dual x)) (gammaR b (F.dual x1))) =
      - gmul (gammaR q x1) (gmul (gammaR b (F.dual x1)) (gammaR a (F.dual x))) :=
    fun x x1 => by rw [gammaR_anticomm a b, gmul_neg_right]
  simp only [e, gtens_neg_left, Finset.sum_neg_distrib]
  simp only [sum_gtens_tri_Omega, Finset.sum_neg_distrib, neg_neg]


theorem quartA (p q a b : I n) :
    ∑ x : F.K, ∑ x1 : F.K, ∑ x2 : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) p (F.dual x2))
      (gmul (gammaR q x) (gmul (gammaR a (F.dual x)) (gammaR b (F.dual x1)))))
      (Sof x2 x1 : OspMod F n) =
    - ∑ x1 : F.K, ∑ x2 : F.K, gtens (gmul (gammaR p (F.dual x2))
      (gmul (OmegaR q a) (gammaR b (F.dual x1)))) (Sof x2 x1) := by
  rw [sum_perm3, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x1 _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun x2 _ => sum_gtens_pre_tri_Omega _ q a _ _

theorem quartB (p q a b : I n) :
    ∑ x : F.K, ∑ x1 : F.K, ∑ x2 : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) p x)
      (gmul (gammaR q (F.dual x2)) (gmul (gammaR a (F.dual x)) (gammaR b (F.dual x1)))))
      (Sof x2 x1 : OspMod F n) =
    ∑ x1 : F.K, ∑ x2 : F.K, gtens (gmul (OmegaR p a)
      (gmul (gammaR q (F.dual x2)) (gammaR b (F.dual x1)))) (Sof x2 x1) := by
  have e : ∀ x x1 x2 : F.K, gmul (gammaR (F := F) (n := n) (r := r) p x)
      (gmul (gammaR q (F.dual x2)) (gmul (gammaR a (F.dual x)) (gammaR b (F.dual x1)))) =
      - gmul (gammaR p x) (gmul (gammaR a (F.dual x))
        (gmul (gammaR q (F.dual x2)) (gammaR b (F.dual x1)))) :=
    fun x x1 x2 => by
      rw [gmul_swap12_gamma (p := q) (q := a) (a := F.dual x2) (b := F.dual x)
        (gammaR b (F.dual x1)), gmul_neg_right]
  simp only [e, gtens_neg_left, Finset.sum_neg_distrib]
  rw [sum_perm3]
  simp only [sum_gtens_tri_Omega, Finset.sum_neg_distrib, neg_neg]

theorem quartC (p q a b : I n) :
    ∑ x : F.K, ∑ x1 : F.K, ∑ x2 : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) p (F.dual x2))
      (gmul (gammaR q x1) (gmul (gammaR a (F.dual x)) (gammaR b (F.dual x1)))))
      (Sof x2 x : OspMod F n) =
    ∑ x : F.K, ∑ x2 : F.K, gtens (gmul (gammaR p (F.dual x2))
      (gmul (OmegaR q b) (gammaR a (F.dual x)))) (Sof x2 x) := by
  have e : ∀ x x1 x2 : F.K, gmul (gammaR (F := F) (n := n) (r := r) p (F.dual x2))
      (gmul (gammaR q x1) (gmul (gammaR a (F.dual x)) (gammaR b (F.dual x1)))) =
      - gmul (gammaR p (F.dual x2)) (gmul (gammaR q x1)
        (gmul (gammaR b (F.dual x1)) (gammaR a (F.dual x)))) :=
    fun x x1 x2 => by rw [gammaR_anticomm a b, gmul_neg_right, gmul_neg_right]
  have e2 : ∀ x : F.K, ∑ x1 : F.K, ∑ x2 : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) p
      (F.dual x2)) (gmul (gammaR q x1) (gmul (gammaR b (F.dual x1)) (gammaR a (F.dual x)))))
      (Sof x2 x : OspMod F n) = - ∑ x2 : F.K, gtens (gmul (gammaR p (F.dual x2))
      (gmul (OmegaR q b) (gammaR a (F.dual x)))) (Sof x2 x) := fun x => by
    rw [Finset.sum_comm]
    simp only [sum_gtens_pre_tri_Omega, Finset.sum_neg_distrib]
  simp only [e, gtens_neg_left, Finset.sum_neg_distrib, e2, neg_neg]

theorem tri_last_first_gamma {p q a : I n} {x y z : F.K} :
    gmul (gammaR (F := F) (n := n) (r := r) p x) (gmul (gammaR q y) (gammaR a z)) =
      gmul (gammaR a z) (gmul (gammaR p x) (gammaR q y)) :=
  (tri_cyc (gammaR_odd _ _) (gammaR_odd _ _) (gammaR_odd _ _)).trans
    (tri_cyc (gammaR_odd _ _) (gammaR_odd _ _) (gammaR_odd _ _))

theorem quartD (p q a b : I n) :
    ∑ x : F.K, ∑ x1 : F.K, ∑ x2 : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) p x1)
      (gmul (gammaR q (F.dual x2)) (gmul (gammaR a (F.dual x)) (gammaR b (F.dual x1)))))
      (Sof x2 x : OspMod F n) =
    - ∑ x : F.K, ∑ x2 : F.K, gtens (gmul (OmegaR p b)
      (gmul (gammaR q (F.dual x2)) (gammaR a (F.dual x)))) (Sof x2 x) := by
  have e : ∀ x x1 x2 : F.K, gmul (gammaR (F := F) (n := n) (r := r) p x1)
      (gmul (gammaR q (F.dual x2)) (gmul (gammaR a (F.dual x)) (gammaR b (F.dual x1)))) =
      gmul (gammaR p x1) (gmul (gammaR b (F.dual x1))
        (gmul (gammaR q (F.dual x2)) (gammaR a (F.dual x)))) :=
    fun x x1 x2 => by rw [tri_last_first_gamma (p := q) (q := a) (a := b)]
  simp only [e]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun x2 _ => sum_gtens_tri_Omega p b _ _

theorem sumS_swap (a b : I n) :
    ∑ x : F.K, ∑ x1 : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) a (F.dual x1))
      (gammaR b (F.dual x))) (Sof x1 x : OspMod F n) =
    ∑ x : F.K, ∑ x1 : F.K, gtens (gmul (gammaR a (F.dual x)) (gammaR b (F.dual x1))) (Sof x x1) :=
  Finset.sum_comm

theorem Omega_even (p q : I n) : IsEvenGR (OmegaR (F := F) (r := r) p q) :=
  (HasCard_OmegaR p q).isEven (by norm_num)

theorem gmul_gmul_Omega (p q : I n) (x y : GR F n r) :
    gmul x (gmul (OmegaR (F := F) (r := r) p q) y) = gmul (OmegaR p q) (gmul x y) :=
  gmul_left_comm_of_even (Omega_even p q) x y

theorem gmul_gmul_Omega' (p q : I n) (x y : GR F n r) :
    gmul x (gmul y (OmegaR (F := F) (r := r) p q)) = gmul (OmegaR p q) (gmul x y) := by
  rw [← gmul_comm_of_even (Omega_even p q) y, gmul_left_comm_of_even (Omega_even p q)]

theorem gmul_JmOmega' (a : GR F n r) (u w : I n) :
    gmul a (JmOmega (F := F) (r := r) u w) = (J n u w) • a - gmul a (OmegaR u w) := by
  unfold JmOmega
  rw [gmul_sub_right', gmul_JR_right, ← rsmul_eq_C_smul]

-- one large `simp` normalizes both sides; the closing `module` needs its result
theorem VecLF2 (u v : I n) (h1 : Bmn.IKey u ≤ Bmn.IKey v) (w : I n) (i : F.K) :
    liftB (bracketJBasis0 JmOmega) (VBasis0 (gammaR (F := F) (n := n) (r := r))
        (Sum.inl ⟨(u, v), h1⟩)) (VBasis0 gammaR (Fof w i)) =
    linM (VBasis0 gammaR) (Bbeta (Sum.inl ⟨(u, v), h1⟩) (Fof w i)) := by
  have hLof : (Lof u v : OspBasis F n) = Sum.inl ⟨(u, v), h1⟩ := Lof_of_le h1
  rw [V0_L, V0_F, hLof]
  simp only [liftB_sub_left, liftB_add_left, liftB_add_right, liftB_rsmul_left, liftB_rsmul_right,
    liftB_sum_left, liftB_sum_right, liftBJ_eN_eN, liftBJ_eN_Sof, liftBJ_Sof_eN, liftBJ_Sof_Sof,
    parity_Fof, sigPow_gone, sigPow_one_gammaR, gone_gmul, gmul_gone, bracket0_Fof_Sof_gen,
    bracket0_Sof_Fof_gen, bracket0_Sof_Sof_gen, parity_inl, bracket0_L_Sof, sigPow_zero]
  have e1 : B0data (r := r) (Sum.inl ⟨(u, v), h1⟩ : OspBasis F n) (Fof w i) =
      gtens gone (bracketLF u v w i) := rfl
  have e2 : PhiG (r := r) (GammaLF u v w i : OspMod F n) =
      (1 / 2 : ℚ) • (gtens (gammaR u i) (eN (Lof v w)) + gtens (gammaR v i) (eN (Lof u w))) := by
    unfold GammaLF
    rw [PhiG_rsmul, PhiG_add, PhiG_beta _ _ _ (fun W => IsQ_eN _ W),
      PhiG_beta _ _ _ (fun W => IsQ_eN _ W)]
  have eG : (GammaBasis (Sum.inl ⟨(u, v), h1⟩ : OspBasis F n) (Fof w i) : OspMod F n) =
      GammaLF u v w i := rfl
  rw [Bbeta_eq_PhiG, e1, eG, e2, bracketJBasis0_L_F]
  simp only [bracketJBasis0_F_F, bracketLF, gsmul_add_right, gsmul_rsmul_right,
    gsmul_gtens, gtens_add_right, gtens_rsmul_right, gtens_zero_right,
    linM_add, linM_rsmul, linM_gtens', extT_eN, V0_F, V0_Lof, gsmul_sum_right]
  simp only [bracketSF, bracketSS, FermionIndex.g, mul_ite, mul_one, mul_zero, ite_smul, one_smul,
    zero_smul, gtens_ite, gtens_add_right, gtens_sub_right,
    smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.smul_sum, gtens_neg_left, gmul_neg_right,
    neg_sub, gmul_JmOmega']
  simp only [one_div, eq_dual_iff, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, F.dual_dual,
    smul_ite, smul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, smul_neg,
    Finset.sum_neg_distrib, sub_neg_eq_add, zero_add]
  simp only [gmul_assoc, gmul_gone, gone_gmul, gtens_sub_left,
    ← gtens_rsmul_left, gsmul_gtens, gsmul_add_right, gsmul_sub_right, gsmul_sum_right,
    gsmul_rsmul_right, smul_add, smul_sub, smul_smul,
    Finset.sum_sub_distrib, ← Finset.smul_sum]
  have hOc : ∀ (a : GR F n r) (p q : I n), gmul a (OmegaR (F := F) (r := r) p q) =
      gmul (OmegaR p q) a := fun a p q =>
    (gmul_comm_of_even ((HasCard_OmegaR (F := F) (r := r) p q).isEven (by norm_num)) a).symm
  have hQ1 : ∑ x : F.K, ∑ x1 : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) u (F.dual x1))
      (gmul (gammaR v x) (gammaR w (F.dual x)))) (Sof x1 i : OspMod F n) =
      - ∑ x1 : F.K, gtens (gmul (OmegaR v w) (gammaR u (F.dual x1))) (Sof x1 i) := by
    rw [Finset.sum_comm]
    simp only [← hOc, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x1 _ => ?_
    exact sum_gtens_pair_Omega' v w _ _
  have hQ2 : ∑ x : F.K, ∑ x1 : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) u x)
      (gmul (gammaR v (F.dual x1)) (gammaR w (F.dual x)))) (Sof x1 i : OspMod F n) =
      ∑ x1 : F.K, gtens (gmul (OmegaR u w) (gammaR v (F.dual x1))) (Sof x1 i) := by
    have e : ∀ x x1 : F.K, gmul (gammaR (F := F) (n := n) (r := r) u x)
        (gmul (gammaR v (F.dual x1)) (gammaR w (F.dual x))) =
        - gmul (gammaR u x) (gmul (gammaR w (F.dual x)) (gammaR v (F.dual x1))) :=
      fun x x1 => by rw [gammaR_anticomm v w, gmul_neg_right]
    simp only [e, gtens_neg_left, Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    simp only [sum_gtens_tri_Omega, Finset.sum_neg_distrib, neg_neg]
  have hQ3 : ∑ x : F.K, ∑ x1 : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) u (F.dual x1))
      (gmul (gammaR v i) (gammaR w (F.dual x)))) (Sof x1 x : OspMod F n) =
      - ∑ x : F.K, ∑ x1 : F.K, gtens (gmul (gammaR v i)
        (gmul (gammaR u (F.dual x)) (gammaR w (F.dual x1)))) (Sof x x1) := by
    rw [Finset.sum_comm (f := fun x x1 => gtens (gmul (gammaR (F := F) (n := n) (r := r) v i)
        (gmul (gammaR u (F.dual x)) (gammaR w (F.dual x1)))) (Sof x x1 : OspMod F n)),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x1 _ => ?_
    rw [tri_swap12_gamma, gtens_neg_left]
  have hQ4 : ∑ x : F.K, ∑ x1 : F.K, gtens (gmul (gammaR (F := F) (n := n) (r := r) u i)
      (gmul (gammaR v (F.dual x1)) (gammaR w (F.dual x)))) (Sof x1 x : OspMod F n) =
      ∑ x : F.K, ∑ x1 : F.K, gtens (gmul (gammaR u i)
        (gmul (gammaR v (F.dual x)) (gammaR w (F.dual x1)))) (Sof x x1) := by
    rw [Finset.sum_comm]
  rw [hQ1, hQ2, hQ3, hQ4]
  have hA1 : ∀ p : F.K, gmul (gammaR (F := F) (n := n) (r := r) u p) (gammaR v i) =
      - gmul (gammaR v i) (gammaR u p) := fun p => gammaR_anticomm _ _ _ _
  simp only [hOc, hA1, sum_gtens_Omega', gtens_neg_left, smul_neg, Finset.sum_neg_distrib]
  module

theorem bracketJBasis0_L_L (J' : I n → I n → GR F n r) (u v s t : I n)
    (h1 : Bmn.IKey u ≤ Bmn.IKey v) (h2 : Bmn.IKey s ≤ Bmn.IKey t) :
    bracketJBasis0 J' (Sum.inl ⟨(u, v), h1⟩) (Sum.inl ⟨(s, t), h2⟩) =
      (1 / 2 : ℚ) • (gtens (J' v s) (eN (Lof u t)) + gtens (J' u s) (eN (Lof v t))
        + gtens (J' v t) (eN (Lof u s)) + gtens (J' u t) (eN (Lof v s))) := rfl

-- one large `simp` normalizes both sides; the closing `module` needs its result
theorem VecLL2 (u v : I n) (h1 : Bmn.IKey u ≤ Bmn.IKey v) (s t : I n)
    (h2 : Bmn.IKey s ≤ Bmn.IKey t) :
    liftB (bracketJBasis0 JmOmega) (VBasis0 (gammaR (F := F) (n := n) (r := r))
        (Sum.inl ⟨(u, v), h1⟩)) (VBasis0 gammaR (Sum.inl ⟨(s, t), h2⟩)) =
    linM (VBasis0 gammaR) (Bbeta (Sum.inl ⟨(u, v), h1⟩) (Sum.inl ⟨(s, t), h2⟩)) := by
  have hLof1 : (Lof u v : OspBasis F n) = Sum.inl ⟨(u, v), h1⟩ := Lof_of_le h1
  have hLof2 : (Lof s t : OspBasis F n) = Sum.inl ⟨(s, t), h2⟩ := Lof_of_le h2
  have eL1 := V0_L (F := F) (n := n) (r := r) u v h1
  have eL2 := V0_L (F := F) (n := n) (r := r) s t h2
  rw [eL1, eL2, hLof1, hLof2]
  simp only [liftB_sub_left, liftB_sub_right, liftB_add_left, liftB_add_right, liftB_rsmul_left,
    liftB_rsmul_right, liftB_sum_left, liftB_sum_right, liftBJ_eN_eN, liftBJ_eN_Sof,
    liftBJ_Sof_eN, liftBJ_Sof_Sof, parity_Fof, parity_inl, sigPow_gone, sigPow_one_gammaR,
    gone_gmul, gmul_gone, bracket0_Fof_Sof_gen, bracket0_Sof_Fof_gen, bracket0_Sof_Sof_gen,
    bracket0_L_Sof, bracket0_Sof_Lof_inl, sigPow_gmul, gmul_neg_left, gmul_neg_right, neg_neg,
    sigPow_zero, gtens_zero_right]
  have e1 : B0data (r := r) (Sum.inl ⟨(u, v), h1⟩ : OspBasis F n) (Sum.inl ⟨(s, t), h2⟩) =
      gtens gone (bracketLL u v s t) := rfl
  have eG : (GammaBasis (Sum.inl ⟨(u, v), h1⟩ : OspBasis F n) (Sum.inl ⟨(s, t), h2⟩) :
      OspMod F n) = 0 := rfl
  rw [Bbeta_eq_PhiG, e1, eG, PhiG_zero, add_zero]
  simp only [bracketJBasis0_L_L, bracketJBasis0_L_F, bracketJBasis0_F_L, bracketJBasis0_F_F,
    bracketLL, gsmul_add_right, gsmul_sub_right,
    gsmul_rsmul_right, gsmul_gtens, gone_gmul, linM_add, linM_rsmul, linM_gtens',
    extT_eN, V0_Lof, gtens_add_right, gtens_rsmul_right, gsmul_sum_right, Finset.sum_const_zero,
    smul_zero, zero_add, gsmul_neg_right]
  simp only [bracketSF, bracketSS, FermionIndex.g, mul_ite, mul_one, mul_zero, ite_smul, one_smul,
    zero_smul, gtens_ite, gtens_add_right, gtens_sub_right,
    smul_add, smul_sub, smul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, Finset.smul_sum, gtens_neg_left, gmul_neg_left,
    neg_sub, gtens_JmOmega, gmul_JmOmega', gmul_assoc, gmul_gone,
    gtens_sub_left, ← gtens_rsmul_left]
  simp [Finset.sum_ite_irrel, Finset.sum_ite_eq', F.dual_dual,
    eq_dual_iff]
  simp only [← Finset.smul_sum]
  simp only [cubA, cubB, cubC, cubD, quartA, quartB, quartC, quartD]
  have hJ1 : J n s u = -J n u s := Bmn.J_antisymm s u
  have hJ2 : J n t u = -J n u t := Bmn.J_antisymm t u
  have hJ3 : J n s v = -J n v s := Bmn.J_antisymm s v
  have hJ4 : J n t v = -J n v t := Bmn.J_antisymm t v
  have hO1 : OmegaR (F := F) (r := r) s u = -OmegaR u s := OmegaR_antisymm u s
  have hO2 : OmegaR (F := F) (r := r) t u = -OmegaR u t := OmegaR_antisymm u t
  have hO3 : OmegaR (F := F) (r := r) s v = -OmegaR v s := OmegaR_antisymm v s
  have hO4 : OmegaR (F := F) (r := r) t v = -OmegaR v t := OmegaR_antisymm v t
  have hOc : ∀ (a : GR F n r) (p q : I n), gmul a (OmegaR (F := F) (r := r) p q) =
      gmul (OmegaR p q) a := fun a p q => (gmul_comm_of_even (Omega_even p q) a).symm
  simp only [hJ1, hJ2, hJ3, hJ4, hO1, hO2, hO3, hO4, hOc, gmul_gmul_Omega,
    sumS_swap, sum_gtens_Omega', gtens_neg_left, smul_neg, neg_smul, Finset.sum_neg_distrib,
    neg_neg, smul_smul, gmul_neg_right]
  module

theorem vChi_bracket' (x y : RModM F n r) :
    bracketJM JmOmega (VChi gammaR x) (VChi gammaR y) = VChi gammaR (bracketBetaM x y) := by
  rw [VChi_eq_linM, bracketJM_eq_liftB, bracketBetaM_eq_liftB]
  refine lift_intertwine_vec (VBasis0 gammaR) (VBasis0 gammaR) (bracketJBasis0 JmOmega) Bbeta
    VBasis0_parity (fun Z Z' => ?_) x y
  rcases Z with ⟨⟨u, v⟩, h1⟩ | ⟨⟨i, j⟩, h1⟩ | ⟨s, i⟩ <;>
  rcases Z' with ⟨⟨a, b⟩, h2⟩ | ⟨⟨k, l⟩, h2⟩ | ⟨t, m⟩
  · exact VecLL2 u v h1 a b h2
  · exact VecLS2 u v h1 k l h2
  · exact VecLF2 u v h1 t m
  · exact VecSL2 i j h1 a b h2
  · exact VecSS2 i j k l h1 h2
  · exact VecSF2 i j h1 t m
  · exact VecFL2 s i a b h2
  · exact VecFS2 k l h2 s i
  · exact VecFF2 s t i m

end Multi
end OspN
end OspOddDeformations

