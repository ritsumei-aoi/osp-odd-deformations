import OspOddDeformations.OspN.Presented.MultiLifts
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.RingTheory.Flat.Domain
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Products of the `κ_s`, `R_r` inside `A_β`, and Prop 3.3 over `R_r`

The ordered products `κ_S` multiply with the sign of `Multi.gs` (`κS_mul_κS`), so
`embG : GR → A_β` is multiplicative and carries the coordinate-level `γ`, `Ω`, `Θ` to those of
`MultiDefs` and `MultiUntwist`.
-/

namespace OspOddDeformations
namespace OspN
namespace Presented

open Bmn (I J)
open scoped TensorProduct

variable {F : FermionIndex} {n r : ℕ} (β' : Fin r → I n → F.K → Multi.PmnR F n r)

/-- The number of inversions of a list: pairs `x` before `y` with `y < x`. -/
def invL : List (Fin r) → ℕ
  | [] => 0
  | x :: l => (l.filter (· < x)).length + invL l

/-- `κ_x` moved into a strictly increasing product. -/
theorem κM_mul_prod_orderedInsert (x : Fin r) (L : List (Fin r)) (hL : L.Pairwise (· < ·))
    (hx : x ∉ L) :
    κM _ _ β' x * (L.map (κM (jR F n r) (gR F n r) β')).prod
      = ((-1 : ℚ) ^ (L.filter (· < x)).length)
        • ((L.orderedInsert (· ≤ ·) x).map (κM _ _ β')).prod := by
  induction L with
  | nil => simp
  | cons y L ih =>
    have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self)
    have hxL : x ∉ L := fun h => hx (List.mem_cons_of_mem _ h)
    have hL' : L.Pairwise (· < ·) := (List.pairwise_cons.mp hL).2
    by_cases hle : x ≤ y
    · have hlt : x < y := lt_of_le_of_ne hle hxy
      have hf : (y :: L).filter (· < x) = [] := by
        rw [List.filter_eq_nil_iff]
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · simpa using (not_lt.mpr hle)
        · have := (List.pairwise_cons.mp hL).1 z hz
          simpa using not_lt.mpr (lt_trans hlt this).le
      rw [hf, List.orderedInsert_cons]
      simp [hle]
    · have hlt : y < x := lt_of_not_ge hle
      rw [List.orderedInsert_cons, List.filter_cons_of_pos (by simpa using hlt)]
      simp only [hle, ↓reduceIte]
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      rw [← mul_assoc, κM_mul_κM, neg_mul, mul_assoc, ih hL' hxL, mul_smul_comm, pow_succ',
        neg_one_mul, neg_smul]

theorem sort_pairwise_lt (S : Finset (Fin r)) : (S.sort (· ≤ ·)).Pairwise (· < ·) :=
  ((Finset.pairwise_sort S _).and (Finset.sort_nodup S _)).imp fun h => lt_of_le_of_ne h.1 h.2

theorem sort_insert_eq (x : Fin r) (T : Finset (Fin r)) (hx : x ∉ T) :
    (insert x T).sort (· ≤ ·) = (T.sort (· ≤ ·)).orderedInsert (· ≤ ·) x := by
  apply List.Perm.eq_of_pairwise' (Finset.pairwise_sort _ _)
    ((Finset.pairwise_sort T _).orderedInsert x _)
  refine (List.perm_of_nodup_nodup_toFinset_eq (Finset.sort_nodup _ _) ?_ ?_).trans
    (List.perm_orderedInsert _ x _).symm
  · exact List.nodup_cons.mpr ⟨by simpa [Finset.mem_sort] using hx, Finset.sort_nodup _ _⟩
  · simp [Finset.sort_toFinset]

theorem length_filter_sort (l : List (Fin r)) (hl : l.Nodup) (x : Fin r) :
    ((l.toFinset.sort (· ≤ ·)).filter (· < x)).length = (l.filter (· < x)).length := by
  have hp : List.Perm (l.toFinset.sort (· ≤ ·)) l :=
    List.perm_of_nodup_nodup_toFinset_eq (Finset.sort_nodup _ _) hl (by simp [Finset.sort_toFinset])
  exact (hp.filter _).length_eq

/-- The product of a list of distinct `κ_s` is `(−1)^{inversions}` times the ordered product. -/
theorem prod_nodup (l : List (Fin r)) (hl : l.Nodup) :
    (l.map (κM (jR F n r) (gR F n r) β')).prod = ((-1 : ℚ) ^ invL l) • κS β' l.toFinset := by
  induction l with
  | nil => simp [κS, invL]
  | cons x l ih =>
    obtain ⟨hx, hl'⟩ := List.nodup_cons.mp hl
    have hxT : x ∉ l.toFinset.sort (· ≤ ·) := by simpa [Finset.mem_sort] using hx
    rw [List.map_cons, List.prod_cons, ih hl', mul_smul_comm, κS,
      κM_mul_prod_orderedInsert β' x _ (sort_pairwise_lt _) hxT, smul_smul,
      ← sort_insert_eq x _ (by simpa using hx), length_filter_sort l hl', List.toFinset_cons, κS,
      invL, pow_add, mul_comm]

theorem invL_sorted (L : List (Fin r)) (hL : L.Pairwise (· < ·)) : invL L = 0 := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [invL, ih (List.pairwise_cons.mp hL).2, add_zero, List.length_eq_zero_iff,
      List.filter_eq_nil_iff]
    intro z hz
    simpa using not_lt.mpr ((List.pairwise_cons.mp hL).1 z hz).le

theorem invL_append_sorted (L₁ L₂ : List (Fin r)) (h₁ : L₁.Pairwise (· < ·))
    (h₂ : L₂.Pairwise (· < ·)) :
    invL (L₁ ++ L₂) = (L₁.map fun x => (L₂.filter (· < x)).length).sum := by
  induction L₁ with
  | nil => simpa using invL_sorted L₂ h₂
  | cons x L ih =>
    have hL : (L.filter (· < x)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro z hz
      simpa using not_lt.mpr ((List.pairwise_cons.mp h₁).1 z hz).le
    rw [List.cons_append, invL, ih (List.pairwise_cons.mp h₁).2, List.filter_append, hL,
      List.nil_append, List.map_cons, List.sum_cons]

theorem card_inversions (S T : Finset (Fin r)) :
    ((S ×ˢ T).filter (fun p => p.2 < p.1)).card
      = ((S.sort (· ≤ ·)).map fun x => ((T.sort (· ≤ ·)).filter (· < x)).length).sum := by
  rw [Finset.card_filter, Finset.sum_product]
  have h : ∀ x, ((T.sort (· ≤ ·)).filter (· < x)).length = ∑ t ∈ T, if t < x then 1 else 0 := by
    intro x
    rw [← Finset.card_filter, ← List.toFinset_card_of_nodup ((Finset.sort_nodup _ _).filter _),
      List.toFinset_filter, Finset.sort_toFinset]
    simp
  simp only [h]
  conv_lhs => rw [← Finset.sort_toFinset S (· ≤ ·)]
  rw [List.sum_toFinset _ (Finset.sort_nodup _ _)]

/-- `κ_S κ_T = gs(S,T) κ_{S∪T}`. -/
theorem κS_mul_κS (S T : Finset (Fin r)) :
    κS β' S * κS β' T = (Multi.gs S T : ℚ) • κS β' (S ∪ T) := by
  have hSS := Finset.sort_toFinset S (· ≤ ·)
  have hTT := Finset.sort_toFinset T (· ≤ ·)
  rw [κS, κS, ← List.prod_append, ← List.map_append]
  by_cases hd : Disjoint S T
  · have hnd : (S.sort (· ≤ ·) ++ T.sort (· ≤ ·)).Nodup := by
      refine List.Nodup.append (Finset.sort_nodup _ _) (Finset.sort_nodup _ _) ?_
      intro a ha hb
      exact Finset.disjoint_left.mp hd ((Finset.mem_sort _).mp ha) ((Finset.mem_sort _).mp hb)
    rw [prod_nodup _ _ hnd, invL_append_sorted _ _ (sort_pairwise_lt S) (sort_pairwise_lt T),
      ← card_inversions, List.toFinset_append, hSS, hTT, Multi.gs]
    simp only [hd, ↓reduceIte]
  · have hnd : ¬ (S.sort (· ≤ ·) ++ T.sort (· ≤ ·)).Nodup := by
      intro h
      apply hd
      rw [Finset.disjoint_left]
      intro a ha hb
      exact List.disjoint_of_nodup_append h ((Finset.mem_sort _).mpr ha)
        ((Finset.mem_sort _).mpr hb)
    rw [prod_eq_zero_of_not_nodup _ hnd, Multi.gs]
    simp only [hd, ↓reduceIte, zero_smul]

/-! ## `embG` -/

theorem embG_add (a b : Multi.GR F n r) : embG β' (a + b) = embG β' a + embG β' b := by
  simp only [embG, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem embG_zero : embG β' (0 : Multi.GR F n r) = 0 := by simp [embG]

theorem embG_neg (a : Multi.GR F n r) : embG β' (-a) = -embG β' a := by
  simp only [embG, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]

theorem embG_sum {ι : Type} (s : Finset ι) (f : ι → Multi.GR F n r) :
    embG β' (∑ i ∈ s, f i) = ∑ i ∈ s, embG β' (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [embG_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, embG_add, ih]

theorem embG_rat_smul (q : ℚ) (a : Multi.GR F n r) :
    embG β' (q • a) = algebraMap ℚ (Multi.PmnR F n r) q • embG β' a := by
  simp only [embG, Pi.smul_apply, Algebra.smul_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [map_mul, mul_assoc]

theorem embG_gmono (S : Finset (Fin r)) (c : Multi.PmnR F n r) :
    embG β' (Multi.gmono S c) = c • κS β' S := by
  rw [embG, Finset.sum_eq_single S]
  · simp [Multi.gmono]
  · intro T _ hT; simp [Multi.gmono, hT]
  · intro h; exact absurd (Finset.mem_univ S) h

theorem κS_singleton (s : Fin r) : κS β' {s} = κM _ _ β' s := by simp [κS]

theorem κS_empty : κS β' (∅ : Finset (Fin r)) = 1 := by simp [κS]

/-- `embG(1) = 1`. -/
theorem embG_one : embG β' (Multi.gone : Multi.GR F n r) = 1 := by
  rw [show (Multi.gone : Multi.GR F n r) = Multi.gmono ∅ 1 by
    funext T; simp [Multi.gone, Multi.gmono], embG_gmono, κS_empty, one_smul]

/-- `embG` is multiplicative. -/
theorem embG_mul (a b : Multi.GR F n r) :
    embG β' (Multi.gmul a b) = embG β' a * embG β' b := by
  have rhs : embG β' a * embG β' b
      = ∑ A, ∑ B, (Multi.gs A B • (a A * b B)) • κS β' (A ∪ B) := by
    rw [embG, embG, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
    rw [smul_mul_smul_comm, κS_mul_κS, smul_comm (a A * b B), smul_assoc]
  rw [rhs, embG]
  simp only [Multi.gmul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun B _ => ?_
  simp [ite_smul, Finset.sum_ite_eq]

/-- `embG(γ_{u,i*}) = γ_{u,i}` of `MultiDefs`. -/
theorem embG_gammaR (u : I n) (i : F.K) :
    embG β' (Multi.gammaR u (F.dual i)) = gammaM (deltaR F n r) u i := by
  rw [Multi.gammaR, embG_sum, gammaM]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [embG_gmono, κS_singleton]
  rfl

theorem embG_gammaR' (u : I n) (i : F.K) :
    embG β' (Multi.gammaR u i) = gammaM (deltaR F n r) u (F.dual i) := by
  rw [← embG_gammaR, F.dual_dual]

/-- `embG(Ω_{uv}) = Ω_{uv}` of `MultiDefs`. -/
theorem embG_OmegaR (u v : I n) :
    embG β' (Multi.OmegaR u v) = omegaM (deltaR F n r) u v := by
  rw [Multi.OmegaR, embG_neg, embG_sum, omegaM_eq]
  simp only [embG_mul, embG_gammaR', F.dual_dual]
  have hg : ∀ i, ∑ j, gR F n r j i • (gammaM (J := jR F n r) (g := gR F n r) (β := β')
      (deltaR F n r) v i * gammaM (deltaR F n r) u j)
      = gammaM (deltaR F n r) v i * gammaM (deltaR F n r) u (F.dual i) := by
    intro i
    rw [Finset.sum_eq_single (F.dual i)]
    · simp [gR, FermionIndex.g, F.dual_dual]
    · intro j _ hj
      have : i ≠ F.dual j := fun h => hj (by rw [h, F.dual_dual])
      simp [gR, FermionIndex.g, this]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [hg]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gammaM_mul_gammaM, neg_neg]

theorem embG_JR (u v : I n) :
    embG β' (Multi.JR (F := F) (r := r) u v) = algebraMap _ (AM F n r β') (jR F n r u v) := by
  rw [show (Multi.JR (F := F) (r := r) u v) = Multi.gmono ∅ (MvPolynomial.C (Bmn.J n u v)) by
    funext T; simp [Multi.JR, Multi.gmono], embG_gmono, κS_empty, Algebra.algebraMap_eq_smul_one,
    jR, MvPolynomial.algebraMap_eq]

theorem embG_QMat (u w : I n) :
    embG β' (Multi.QMat (F := F) (r := r) u w)
      = (OmV (deltaR F n r) β' * JV β' : Matrix (I n) (I n) (AM F n r β')) u w := by
  rw [Multi.QMat, embG_sum, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [embG_mul, embG_OmegaR, embG_JR]
  rfl

theorem embG_QPow (k : ℕ) (u w : I n) :
    embG β' (Multi.QPow (F := F) (r := r) k u w)
      = ((OmV (deltaR F n r) β' * JV β' : Matrix (I n) (I n) (AM F n r β')) ^ k) u w := by
  induction k generalizing u w with
  | zero =>
    rw [pow_zero, Matrix.one_apply, Multi.QPow]
    split_ifs with h
    · simp only [h, ite_true]; exact embG_one β'
    · simp only [h, ite_false]; exact embG_zero β'
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply, Multi.QPow, embG_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [embG_mul, ih, embG_QMat]

/-- `embG(Θ) = Θ` of `MultiUntwist`. -/
theorem embG_thetaSeries (u w : I n) :
    embG β' (Multi.thetaSeries u w) = thetaV (deltaR F n r) β' u w := by
  rw [Multi.thetaSeries, embG_sum, thetaV, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [embG_rat_smul, embG_QPow, Matrix.smul_apply]

theorem embG_thetaSeries_central (u w : I n) (x : AM F n r β') :
    embG β' (Multi.thetaSeries u w) * x = x * embG β' (Multi.thetaSeries u w) := by
  rw [embG_thetaSeries]
  exact thetaV_central u w x

/-! ## The realization over `R_r`: `T = Λ_{P_r}(κ_1,…,κ_r) ⊗̂ A_0` -/

section realize

variable (F n r)

/-- `Λ_{P_r}(κ_1, …, κ_r)`, the Grassmann algebra over `P_r`. -/
noncomputable abbrev RR : Type := ExteriorAlgebra (Multi.PmnR F n r) (Fin r → Multi.PmnR F n r)

/-- Its `ℤ/2`-grading. -/
noncomputable abbrev RRGrading : ZMod 2 → Submodule (Multi.PmnR F n r) (RR F n r) :=
  CliffordAlgebra.evenOdd (0 : QuadraticForm (Multi.PmnR F n r) (Fin r → Multi.PmnR F n r))

noncomputable instance : Algebra ℚ (RR F n r) :=
  Algebra.restrictScalars ℚ (Multi.PmnR F n r) (RR F n r)

instance : IsScalarTower ℚ (Multi.PmnR F n r) (RR F n r) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The grading over `ℚ`. -/
noncomputable abbrev RRGradingQ : ZMod 2 → Submodule ℚ (RR F n r) :=
  fun i => (RRGrading F n r i).restrictScalars ℚ

noncomputable instance : GradedAlgebra (RRGradingQ F n r) :=
  inferInstanceAs (GradedAlgebra fun i => ((CliffordAlgebra.evenOdd
    (0 : QuadraticForm (Multi.PmnR F n r) (Fin r → Multi.PmnR F n r))) i).restrictScalars ℚ)

/-- `T = Λ ⊗̂ A_0`. -/
noncomputable abbrev TR : Type := GradedTensorProduct ℚ (RRGradingQ F n r) (A0Grading F n)

/-- `κ_s` in `Λ`. -/
noncomputable def κR (s : Fin r) : RR F n r :=
  ExteriorAlgebra.ι (Multi.PmnR F n r) (Pi.single s 1)

theorem κR_odd (s : Fin r) : κR F n r s ∈ RRGradingQ F n r 1 :=
  CliffordAlgebra.ι_mem_evenOdd_one _ _

/-- The generators in `T`. -/
noncomputable def BT (u : I n) : TR F n r :=
  GradedTensorProduct.includeRight (RRGradingQ F n r) (A0Grading F n) (Bu0 F n u)
/-- `a_i` in `T`. -/
noncomputable def aT (i : F.K) : TR F n r :=
  GradedTensorProduct.includeRight (RRGradingQ F n r) (A0Grading F n) (aA0 F n i)
/-- `κ_s` in `T`. -/
noncomputable def kT (s : Fin r) : TR F n r :=
  GradedTensorProduct.includeLeft (RRGradingQ F n r) (A0Grading F n) (κR F n r s)
/-- A coefficient of `P_r` in `T`. -/
noncomputable def coefT (c : Multi.PmnR F n r) : TR F n r :=
  GradedTensorProduct.includeLeft (RRGradingQ F n r) (A0Grading F n)
    (algebraMap (Multi.PmnR F n r) (RR F n r) c)

/-- `[B_u, B_v] = J_{uv}` in `A_0` (the inner step of `BuAB_comm`). -/
theorem Bu0_comm (u v : I n) :
    Bu0 F n u * Bu0 F n v - Bu0 F n v * Bu0 F n u = (Bmn.J n u v) • (1 : A0 F n) := by
  simp only [Bu0, ← GradedTensorProduct.includeLeft_apply, ← map_mul, ← map_sub]
  rw [show InhomogeneousDeformations.Source.B n (Bmn.index0nToFun n u)
        * InhomogeneousDeformations.Source.B n (Bmn.index0nToFun n v)
      - InhomogeneousDeformations.Source.B n (Bmn.index0nToFun n v)
        * InhomogeneousDeformations.Source.B n (Bmn.index0nToFun n u)
      = InhomogeneousDeformations.Source.opComm
          (InhomogeneousDeformations.Source.B n (Bmn.index0nToFun n u))
          (InhomogeneousDeformations.Source.B n (Bmn.index0nToFun n v)) from rfl,
    InhomogeneousDeformations.Source.B_comm, JnQ_correspondence0n, map_smul, map_one]

theorem aA0_mul_add_swap (i j : F.K) :
    aA0 F n i * aA0 F n j + aA0 F n j * aA0 F n i = (F.g i j) • (1 : A0 F n) := by
  simp only [aA0, ← GradedTensorProduct.includeRight_apply, ← map_mul, ← map_add,
    a_mul_a_add_swap, map_smul, map_one]

/-- The ordered product `κ_S` in `Λ`. -/
noncomputable def κRS (S : Finset (Fin r)) : RR F n r := ((S.sort (· ≤ ·)).map (κR F n r)).prod

/-- The `κ_S` are mathlib's basis of `Λ`. -/
theorem basis_eq_κRS (S : Finset (Fin r)) :
    (Pi.basisFun (Multi.PmnR F n r) (Fin r)).ExteriorAlgebra S = κRS F n r S := by
  rw [ExteriorAlgebra.basis_apply_ofCard (s_card := rfl)]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, Function.comp_apply, Pi.basisFun_apply,
    κRS]
  change (List.ofFn fun i => ExteriorAlgebra.ι (Multi.PmnR F n r)
    (Pi.single ((S.orderEmbOfFin rfl) i) 1)).prod = _
  congr 1
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp [Finset.orderEmbOfFin_apply, κR]

/-! ### Relations in `T` -/

theorem includeLeft_mul_includeRight (x : RR F n r) (y : A0 F n) :
    GradedTensorProduct.includeLeft (RRGradingQ F n r) (A0Grading F n) x
      * GradedTensorProduct.includeRight (RRGradingQ F n r) (A0Grading F n) y = x ᵍ⊗ₜ[ℚ] y := by
  simp only [GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply]
  exact GradedTensorProduct.tmul_one_mul_one_tmul _ _ x y

theorem includeRight_mul_includeLeft {i j : ZMod 2} (x : RR F n r) (hx : x ∈ RRGradingQ F n r i)
    (y : A0 F n) (hy : y ∈ A0Grading F n j) :
    GradedTensorProduct.includeRight (RRGradingQ F n r) (A0Grading F n) y
      * GradedTensorProduct.includeLeft (RRGradingQ F n r) (A0Grading F n) x
      = ((-1 : ℤˣ) ^ (j * i)) • (x ᵍ⊗ₜ[ℚ] y) := by
  simp only [GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply]
  have h := GradedTensorProduct.tmul_coe_mul_coe_tmul (RRGradingQ F n r) (A0Grading F n)
    (1 : RR F n r) (⟨y, hy⟩ : A0Grading F n j) (⟨x, hx⟩ : RRGradingQ F n r i) (1 : A0 F n)
  simpa using h

theorem BT_comm (u v : I n) :
    BT F n r u * BT F n r v - BT F n r v * BT F n r u = (Bmn.J n u v) • (1 : TR F n r) := by
  simp only [BT, ← map_mul, ← map_sub, Bu0_comm, map_smul, map_one]

theorem aT_mul_add_swap (i j : F.K) :
    aT F n r i * aT F n r j + aT F n r j * aT F n r i = (F.g i j) • (1 : TR F n r) := by
  simp only [aT, ← map_mul, ← map_add, aA0_mul_add_swap, map_smul, map_one]

theorem BT_comm_aT (u : I n) (i : F.K) : BT F n r u * aT F n r i = aT F n r i * BT F n r u := by
  simp only [BT, aT, ← map_mul, aA0_comm_Bu0]

theorem kT_mul_kT (s t : Fin r) : kT F n r s * kT F n r t + kT F n r t * kT F n r s = 0 := by
  simp only [kT, ← map_mul, ← map_add, κR, ExteriorAlgebra.ι_add_mul_swap, map_zero]

theorem kT_sq (s : Fin r) : kT F n r s * kT F n r s = 0 := by
  simp only [kT, ← map_mul, κR, ExteriorAlgebra.ι_sq_zero, map_zero]

theorem kT_comm_BT (s : Fin r) (u : I n) : kT F n r s * BT F n r u = BT F n r u * kT F n r s := by
  rw [kT, BT, includeLeft_mul_includeRight, includeRight_mul_includeLeft F n r _ (κR_odd F n r s)
    _ (Bu0_mem_A0Grading_zero F n u)]
  simp

theorem kT_mul_aT (s : Fin r) (i : F.K) :
    kT F n r s * aT F n r i + aT F n r i * kT F n r s = 0 := by
  rw [kT, aT, includeLeft_mul_includeRight, includeRight_mul_includeLeft F n r _ (κR_odd F n r s)
    _ (aA0_mem_A0Grading_one F n i)]
  simp

theorem coefT_comm (c : Multi.PmnR F n r) (x : TR F n r)
    (hx : x ∈ Set.range (BT F n r) ∪ Set.range (aT F n r) ∪ Set.range (kT F n r)
      ∪ Set.range (coefT F n r)) : coefT F n r c * x = x * coefT F n r c := by
  have hc : algebraMap (Multi.PmnR F n r) (RR F n r) c ∈ RRGradingQ F n r 0 :=
    SetLike.algebraMap_mem_graded (RRGrading F n r) c
  rcases hx with ((⟨u, rfl⟩ | ⟨i, rfl⟩) | ⟨s, rfl⟩) | ⟨d, rfl⟩
  · rw [coefT, BT, includeLeft_mul_includeRight,
      includeRight_mul_includeLeft F n r _ hc _ (Bu0_mem_A0Grading_zero F n u)]
    simp
  · rw [coefT, aT, includeLeft_mul_includeRight,
      includeRight_mul_includeLeft F n r _ hc _ (aA0_mem_A0Grading_one F n i)]
    simp
  · simp only [coefT, kT, ← map_mul, Algebra.commutes]
  · simp only [coefT, ← map_mul, ← map_mul, mul_comm c d]

/-! ### `ρ_r : A_0 → T` -/

/-- `coefT` as a ring homomorphism. -/
noncomputable def coefTHom : Multi.PmnR F n r →+* TR F n r :=
  (GradedTensorProduct.includeLeft (RRGradingQ F n r) (A0Grading F n)).toRingHom.comp
    (algebraMap (Multi.PmnR F n r) (RR F n r))

theorem coefTHom_apply (c : Multi.PmnR F n r) : coefTHom F n r c = coefT F n r c := rfl

theorem coefT_rat (q : ℚ) : coefT F n r (algebraMap ℚ _ q) = q • (1 : TR F n r) := by
  have h : (coefTHom F n r).comp (algebraMap ℚ (Multi.PmnR F n r)) = algebraMap ℚ (TR F n r) :=
    RingHom.ext_rat _ _
  rw [← coefTHom_apply, ← RingHom.comp_apply, h, Algebra.algebraMap_eq_smul_one]

/-- The subalgebra spanned by the generators and the coefficients. -/
noncomputable def SubT : Subalgebra ℚ (TR F n r) :=
  Algebra.adjoin ℚ (Set.range (BT F n r) ∪ Set.range (aT F n r) ∪ Set.range (kT F n r)
    ∪ Set.range (coefT F n r))

theorem coefT_commute_SubT (c : Multi.PmnR F n r) (x : SubT F n r) :
    Commute (coefT F n r c) (x : TR F n r) := by
  obtain ⟨x, hx⟩ := x
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact coefT_comm F n r c y hy
  | algebraMap q => exact Algebra.commute_algebraMap_right q _
  | add y z _ _ hy hz => exact hy.add_right hz
  | mul y z _ _ hy hz => exact hy.mul_right hz

theorem coefT_mem_SubT (c : Multi.PmnR F n r) : coefT F n r c ∈ SubT F n r :=
  Algebra.subset_adjoin <| (Or.inr ⟨c, rfl⟩)

/-- `coefT` into `SubT`. -/
noncomputable def coefSubT : Multi.PmnR F n r →+* SubT F n r :=
  (coefTHom F n r).codRestrict (SubT F n r) (coefT_mem_SubT F n r)

noncomputable instance : Algebra (Multi.PmnR F n r) (SubT F n r) :=
  (coefSubT F n r).toAlgebra' fun c x => Subtype.ext (coefT_commute_SubT F n r c x)

theorem coe_algebraMap_SubT (c : Multi.PmnR F n r) :
    ((algebraMap (Multi.PmnR F n r) (SubT F n r) c : SubT F n r) : TR F n r) = coefT F n r c :=
  rfl

/-- The generators, in `SubT`. -/
noncomputable def realizeGenR : GenM (I n) F.K r → SubT F n r
  | Sum.inl u => ⟨BT F n r u, Algebra.subset_adjoin <| (Or.inl (Or.inl (Or.inl ⟨u, rfl⟩)))⟩
  | Sum.inr (Sum.inl i) =>
    ⟨aT F n r i, Algebra.subset_adjoin <| (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))⟩
  | Sum.inr (Sum.inr s) => ⟨kT F n r s, Algebra.subset_adjoin <| (Or.inl (Or.inr ⟨s, rfl⟩))⟩

theorem realizeGenR_rel (x y : FreeAlgebra (Multi.PmnR F n r) (GenM (I n) F.K r))
    (h : RelM (jR F n r) (gR F n r) 0 x y) :
    FreeAlgebra.lift (Multi.PmnR F n r) (realizeGenR F n r) x
      = FreeAlgebra.lift (Multi.PmnR F n r) (realizeGenR F n r) y := by
  cases h with
  | bb u v =>
    apply Subtype.ext
    simp only [map_mul, map_add, AlgHom.commutes, bMF, FreeAlgebra.lift_ι_apply, realizeGenR,
      Subalgebra.coe_mul, Subalgebra.coe_add, coe_algebraMap_SubT, jR, coefT_rat]
    rw [← sub_eq_iff_eq_add', BT_comm]
  | aa i j =>
    apply Subtype.ext
    simp only [map_mul, map_add, AlgHom.commutes, aMF, FreeAlgebra.lift_ι_apply, realizeGenR,
      Subalgebra.coe_mul, Subalgebra.coe_add, coe_algebraMap_SubT, gR, coefT_rat]
    exact aT_mul_add_swap F n r i j
  | ba u i =>
    apply Subtype.ext
    simp only [map_mul, aMF, bMF, kMF, FreeAlgebra.lift_ι_apply,
      realizeGenR, Subalgebra.coe_mul, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero, add_zero]
    exact BT_comm_aT F n r u i
  | kk s t =>
    apply Subtype.ext
    simp only [map_mul, map_add, map_zero, kMF, FreeAlgebra.lift_ι_apply, realizeGenR,
      Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_zero]
    exact kT_mul_kT F n r s t
  | kss s =>
    apply Subtype.ext
    simp only [map_mul, map_zero, kMF, FreeAlgebra.lift_ι_apply, realizeGenR, Subalgebra.coe_mul,
      Subalgebra.coe_zero]
    exact kT_sq F n r s
  | kb s u =>
    apply Subtype.ext
    simp only [map_mul, kMF, bMF, FreeAlgebra.lift_ι_apply, realizeGenR, Subalgebra.coe_mul]
    exact kT_comm_BT F n r s u
  | ka s i =>
    apply Subtype.ext
    simp only [map_mul, map_add, map_zero, kMF, aMF, FreeAlgebra.lift_ι_apply, realizeGenR,
      Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_zero]
    exact kT_mul_aT F n r s i

/-- `A_0` over `R_r` into `SubT`. -/
noncomputable def realizeR : AM F n r 0 →ₐ[Multi.PmnR F n r] SubT F n r :=
  liftM (realizeGenR F n r) (realizeGenR_rel F n r)

/-- `ρ_r : A_0 → T`. -/
noncomputable def rhoR : AM F n r 0 →+* TR F n r :=
  (SubT F n r).val.toRingHom.comp (realizeR F n r).toRingHom

theorem rhoR_b (u : I n) : rhoR F n r (bM _ _ 0 u) = BT F n r u := by
  simp only [rhoR, bM, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, realizeR,
    liftM_mk, bMF, FreeAlgebra.lift_ι_apply, realizeGenR]
  rfl
theorem rhoR_a (i : F.K) : rhoR F n r (aM _ _ 0 i) = aT F n r i := by
  simp only [rhoR, aM, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, realizeR,
    liftM_mk, aMF, FreeAlgebra.lift_ι_apply, realizeGenR]
  rfl
theorem rhoR_κ (s : Fin r) : rhoR F n r (κM _ _ 0 s) = kT F n r s := by
  simp only [rhoR, κM, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, realizeR,
    liftM_mk, kMF, FreeAlgebra.lift_ι_apply, realizeGenR]
  rfl
theorem rhoR_smul (c : Multi.PmnR F n r) (x : AM F n r 0) :
    rhoR F n r (c • x) = coefT F n r c * rhoR F n r x := by
  rw [Algebra.smul_def, map_mul]
  congr 1
  simp only [rhoR, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    AlgHom.commutes]
  rfl
theorem rhoR_rat_smul (q : ℚ) (x : AM F n r 0) : rhoR F n r (q • x) = q • rhoR F n r x := by
  rw [← algebraMap_smul (Multi.PmnR F n r) q x, rhoR_smul, coefT_rat, smul_one_mul]

theorem rhoR_κS (S : Finset (Fin r)) :
    rhoR F n r (κS 0 S)
      = GradedTensorProduct.includeLeft (RRGradingQ F n r) (A0Grading F n) (κRS F n r S) := by
  simp only [κS, κRS, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro s _
  simp only [Function.comp_apply, rhoR_κ, kT]

theorem rhoR_XpM (X : OspBasis F n) :
    rhoR F n r (XpM 0 X)
      = GradedTensorProduct.includeRight (RRGradingQ F n r) (A0Grading F n) (X0A0 F n X) := by
  match X with
  | .inl ⟨(u, v), _⟩ =>
    simp only [XpM, LpM, rhoR_rat_smul, map_add, map_mul, rhoR_b, BT, X0A0, L0A0, map_smul]
  | .inr (.inl ⟨(i, j), _⟩) =>
    simp only [XpM, SpM, rhoR_rat_smul, map_sub, map_mul, rhoR_a, aT, X0A0, S0A0, map_smul]
  | .inr (.inr (u, i)) =>
    simp only [XpM, FpM, rhoR_rat_smul, map_add, map_mul, rhoR_a, rhoR_b, aT, BT, X0A0, F0A0,
      map_smul]

theorem rhoR_iotaM (x : Multi.RModM F n r) :
    rhoR F n r (iotaM 0 x)
      = ∑ X, (∑ S, x (X, S) • κRS F n r S) ᵍ⊗ₜ[ℚ] X0A0 F n X := by
  rw [iotaM, map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [show (∑ S, x (X, S) • κRS F n r S) ᵍ⊗ₜ[ℚ] X0A0 F n X
      = ∑ S, (x (X, S) • κRS F n r S) ᵍ⊗ₜ[ℚ] X0A0 F n X by
    change GradedTensorProduct.of ℚ _ _ _ = ∑ S, GradedTensorProduct.of ℚ _ _ _
    rw [TensorProduct.sum_tmul, map_sum]]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [rhoR_smul, map_mul, rhoR_κS, rhoR_XpM, ← mul_assoc, coefT, ← map_mul,
    includeLeft_mul_includeRight, Algebra.smul_def]

/-- Over `ℚ`: if `y` is linearly independent, `Σ_X lam_X ⊗ y_X = 0` forces every `lam_X = 0`. -/
theorem coeff_zero {A B ι : Type} [AddCommGroup A] [Module ℚ A] [AddCommGroup B] [Module ℚ B]
    [Fintype ι] (y : ι → B) (hy : LinearIndependent ℚ y) (lam : ι → A)
    (h : ∑ X, lam X ⊗ₜ[ℚ] y X = 0) : lam = 0 := by
  classical
  let Y : (ι → ℚ) →ₗ[ℚ] B := Fintype.linearCombination ℚ y
  have hY : Function.Injective Y := linearIndependent_iff_injective_fintypeLinearCombination.mp hy
  let z : A ⊗[ℚ] (ι → ℚ) := ∑ X, lam X ⊗ₜ[ℚ] Pi.single X 1
  have hz : Y.lTensor A z = 0 := by
    simp only [z, map_sum, LinearMap.lTensor_tmul, Y, Fintype.linearCombination_apply_single,
      one_smul]
    exact h
  have hz0 : z = 0 := Module.Flat.lTensor_preserves_injective_linearMap Y hY (by rw [hz, map_zero])
  have := congrArg (TensorProduct.piScalarRight ℚ ℚ A ι) hz0
  rw [map_zero] at this
  funext j
  have hj := congrFun this j
  simp only [z, map_sum, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    Finset.sum_apply, Pi.single_apply, ite_smul, one_smul, zero_smul] at hj
  simpa [Finset.sum_ite_eq] using hj

end realize

/-- **Prop 3.3 over `R_r`**: `ι_0 : 𝔤_{R_r} → A_0` is injective. -/
theorem iotaM_zero_injective :
    Function.Injective (iotaM (F := F) (n := n) (r := r) 0) := by
  classical
  intro x y h
  have h' := congrArg (rhoR F n r) h
  rw [rhoR_iotaM, rhoR_iotaM] at h'
  let lam : OspBasis F n → RR F n r := fun X => ∑ S, (x (X, S) - y (X, S)) • κRS F n r S
  have hsum : ∑ X, lam X ⊗ₜ[ℚ] X0A0 F n X = 0 := by
    have h2 : GradedTensorProduct.of ℚ (RRGradingQ F n r) (A0Grading F n)
        (∑ X, lam X ⊗ₜ[ℚ] X0A0 F n X) = 0 := by
      simp only [lam, sub_smul, Finset.sum_sub_distrib, TensorProduct.sub_tmul, map_sum, map_sub]
      rw [sub_eq_zero]
      exact h'
    exact (GradedTensorProduct.of ℚ (RRGradingQ F n r) (A0Grading F n)).injective
      (by rw [h2, map_zero])
  have hlam := coeff_zero (X0A0 F n) (X0A0_linearIndependent F n) lam hsum
  funext ⟨X, S⟩
  have hX := congrFun hlam X
  simp only [lam, Pi.zero_apply] at hX
  simp only [← basis_eq_κRS] at hX
  have := (Fintype.linearIndependent_iff.mp
    ((Pi.basisFun (Multi.PmnR F n r) (Fin r)).ExteriorAlgebra.linearIndependent)) _ hX S
  exact sub_eq_zero.mp this

end Presented
end OspN
end OspOddDeformations
