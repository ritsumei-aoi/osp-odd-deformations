import OspOddDeformations.OspN.Presented.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Central.Defs

/-!
# The source algebra over `R_r`, presented, and the matrix `Ω`

`A_β` over `R_r = P_r ⊗ Λ(κ_1,…,κ_r)` (Section 5): generated over `P` by even `b_u`, odd `a_i` and
odd `κ_s`, subject to `[b_u,b_v] = J_{uv}`, `{a_i,a_j} = g_{ij}`,
`[b_u,a_i] = Σ_s β^{(s)}_{u,i} κ_s` (eq. (5.1)), and `κ_s` odd and supercentral:
`{κ_s,κ_t} = 0`, `κ_s² = 0`, `[κ_s,b_u] = 0`, `{κ_s,a_i} = 0`. As in `Defs.lean`, `SrcM J g β` is
a `RingQuot` of the free `P`-algebra, carried by
a type synonym; `β = 0` gives `A_0` over `R_r`.

For coefficients `δ` with `Σ_i δ^{(s)}_{u,i} g_{ji} = β^{(s)}_{u,j}` (in the paper
`δ^{(s)}_{u,i} = β^{(s)}_{u,i*}`), `c_u = Σ_i γ_{u,i} a_i` with `γ_{u,i} = Σ_s δ^{(s)}_{u,i} κ_s`,
and `Ω_{uv} = [c_u, c_v]` (eq. (5.2)).
`Ω` is central and antisymmetric, and every product of more than `r` of the `κ_s` vanishes, so the
entries of `(ΩJ)^k` vanish when `2k > r` (`omega_pow_eq_zero`).
-/

namespace OspOddDeformations
namespace OspN
namespace Presented

variable {P : Type} [CommRing P] {I K : Type} {r : ℕ}

/-- The generators: `b u`, `a i` and `κ s`. -/
abbrev GenM (I K : Type) (r : ℕ) := I ⊕ K ⊕ Fin r

/-- `b_u` in the free algebra. -/
def bMF (u : I) : FreeAlgebra P (GenM I K r) := FreeAlgebra.ι P (Sum.inl u)
/-- `a_i` in the free algebra. -/
def aMF (i : K) : FreeAlgebra P (GenM I K r) := FreeAlgebra.ι P (Sum.inr (Sum.inl i))
/-- `κ_s` in the free algebra. -/
def kMF (s : Fin r) : FreeAlgebra P (GenM I K r) := FreeAlgebra.ι P (Sum.inr (Sum.inr s))

/-- The relations of eq. (5.1). -/
inductive RelM (J : I → I → P) (g : K → K → P) (β : Fin r → I → K → P) :
    FreeAlgebra P (GenM I K r) → FreeAlgebra P (GenM I K r) → Prop
  | bb (u v : I) : RelM J g β (bMF u * bMF v) (bMF v * bMF u + algebraMap P _ (J u v))
  | aa (i j : K) : RelM J g β (aMF i * aMF j + aMF j * aMF i) (algebraMap P _ (g i j))
  | ba (u : I) (i : K) : RelM J g β (bMF u * aMF i) (aMF i * bMF u + ∑ s, β s u i • kMF s)
  | kk (s t : Fin r) : RelM J g β (kMF s * kMF t + kMF t * kMF s) 0
  | kss (s : Fin r) : RelM J g β (kMF s * kMF s) 0
  | kb (s : Fin r) (u : I) : RelM J g β (kMF s * bMF u) (bMF u * kMF s)
  | ka (s : Fin r) (i : K) : RelM J g β (kMF s * aMF i + aMF i * kMF s) 0

/-- The presented source algebra over `R_r`. -/
def SrcM (J : I → I → P) (g : K → K → P) (β : Fin r → I → K → P) : Type := RingQuot (RelM J g β)

instance (J : I → I → P) (g : K → K → P) (β : Fin r → I → K → P) : Ring (SrcM J g β) :=
  inferInstanceAs (Ring (RingQuot _))

instance (J : I → I → P) (g : K → K → P) (β : Fin r → I → K → P) : Algebra P (SrcM J g β) :=
  inferInstanceAs (Algebra P (RingQuot _))

variable (J : I → I → P) (g : K → K → P) (β : Fin r → I → K → P)

/-- The quotient map. -/
def mkM : FreeAlgebra P (GenM I K r) →ₐ[P] SrcM J g β := RingQuot.mkAlgHom P (RelM J g β)

/-- `b_u`. -/
def bM (u : I) : SrcM J g β := mkM J g β (bMF u)
/-- `a_i`. -/
def aM (i : K) : SrcM J g β := mkM J g β (aMF i)
/-- `κ_s`. -/
def κM (s : Fin r) : SrcM J g β := mkM J g β (kMF s)

variable {J g β}

theorem mkM_rel {x y : FreeAlgebra P (GenM I K r)} (h : RelM J g β x y) :
    mkM J g β x = mkM J g β y :=
  RingQuot.mkAlgHom_rel P h

theorem bM_mul_bM (u v : I) :
    bM J g β u * bM J g β v = bM J g β v * bM J g β u + algebraMap P _ (J u v) := by
  simpa [bM, map_mul, map_add, AlgHom.commutes] using
    mkM_rel (J := J) (g := g) (β := β) (RelM.bb u v)
theorem aM_mul_aM_add (i j : K) :
    aM J g β i * aM J g β j + aM J g β j * aM J g β i = algebraMap P _ (g i j) := by
  simpa [aM, map_mul, map_add, AlgHom.commutes] using
    mkM_rel (J := J) (g := g) (β := β) (RelM.aa i j)
theorem bM_mul_aM (u : I) (i : K) :
    bM J g β u * aM J g β i = aM J g β i * bM J g β u + ∑ s, β s u i • κM J g β s := by
  simpa [aM, bM, κM, map_mul, map_add, map_sum, map_smul] using
    mkM_rel (J := J) (g := g) (β := β) (RelM.ba u i)
theorem κM_mul_κM (s t : Fin r) : κM J g β s * κM J g β t = -(κM J g β t * κM J g β s) := by
  have h := mkM_rel (J := J) (g := g) (β := β) (RelM.kk s t)
  simp only [map_mul, map_add, map_zero] at h
  exact eq_neg_of_add_eq_zero_left h
theorem κM_sq (s : Fin r) : κM J g β s * κM J g β s = 0 := by
  simpa [κM, map_mul] using mkM_rel (J := J) (g := g) (β := β) (RelM.kss s)
theorem κM_mul_bM (s : Fin r) (u : I) : κM J g β s * bM J g β u = bM J g β u * κM J g β s := by
  simpa [κM, bM, map_mul] using mkM_rel (J := J) (g := g) (β := β) (RelM.kb s u)
theorem κM_mul_aM (s : Fin r) (i : K) : κM J g β s * aM J g β i = -(aM J g β i * κM J g β s) := by
  have h := mkM_rel (J := J) (g := g) (β := β) (RelM.ka s i)
  simp only [map_mul, map_add, map_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- A map out of `SrcM` given on generators that satisfy the relations. -/
def liftM {A : Type} [Ring A] [Algebra P A] (f : GenM I K r → A)
    (h : ∀ x y, RelM J g β x y → FreeAlgebra.lift P f x = FreeAlgebra.lift P f y) :
    SrcM J g β →ₐ[P] A :=
  RingQuot.liftAlgHom P ⟨FreeAlgebra.lift P f, h⟩

theorem liftM_mk {A : Type} [Ring A] [Algebra P A] (f : GenM I K r → A)
    (h : ∀ x y, RelM J g β x y → FreeAlgebra.lift P f x = FreeAlgebra.lift P f y)
    (x : FreeAlgebra P (GenM I K r)) :
    liftM f h (mkM J g β x) = FreeAlgebra.lift P f x :=
  RingQuot.liftAlgHom_mkAlgHom_apply P _ _ _

theorem algHom_extM {A : Type} [Ring A] [Algebra P A] {φ ψ : SrcM J g β →ₐ[P] A}
    (hb : ∀ u, φ (bM J g β u) = ψ (bM J g β u)) (ha : ∀ i, φ (aM J g β i) = ψ (aM J g β i))
    (hκ : ∀ s, φ (κM J g β s) = ψ (κM J g β s)) : φ = ψ := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext x
  rcases x with u | i | s
  · exact hb u
  · exact ha i
  · exact hκ s

/-- An element commuting with every generator is central. -/
theorem mem_center_of_comm (z : SrcM J g β) (hb : ∀ u, z * bM J g β u = bM J g β u * z)
    (ha : ∀ i, z * aM J g β i = aM J g β i * z) (hκ : ∀ s, z * κM J g β s = κM J g β s * z) :
    z ∈ Subalgebra.center P (SrcM J g β) := by
  rw [Subalgebra.mem_center_iff]
  intro y
  have hs : Function.Surjective (mkM J g β) := RingQuot.mkAlgHom_surjective P _
  obtain ⟨x, rfl⟩ := hs y
  induction x using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes]; exact Algebra.commutes c z
  | grade1 x =>
    rcases x with u | i | s
    · exact (hb u).symm
    · exact (ha i).symm
    · exact (hκ s).symm
  | mul x y hx hy => rw [map_mul, mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  | add x y hx hy => rw [map_add, add_mul, mul_add, hx, hy]

/-- The images of the generators under `parityM`. -/
def parityGenM : GenM I K r → SrcM J g β
  | Sum.inl u => bM J g β u
  | Sum.inr (Sum.inl i) => -aM J g β i
  | Sum.inr (Sum.inr s) => -κM J g β s

theorem parityGenM_rel (x y : FreeAlgebra P (GenM I K r)) (h : RelM J g β x y) :
    FreeAlgebra.lift P (parityGenM (J := J) (g := g) (β := β)) x
      = FreeAlgebra.lift P parityGenM y := by
  cases h with
  | bb u v =>
    simp only [map_mul, map_add, AlgHom.commutes, bMF, FreeAlgebra.lift_ι_apply, parityGenM]
    exact bM_mul_bM u v
  | aa i j =>
    simp only [map_mul, map_add, AlgHom.commutes, aMF, FreeAlgebra.lift_ι_apply, parityGenM,
      neg_mul_neg]
    exact aM_mul_aM_add i j
  | ba u i =>
    simp only [map_mul, map_add, map_sum, map_smul, aMF, bMF, kMF, FreeAlgebra.lift_ι_apply,
      parityGenM, mul_neg, neg_mul, smul_neg, Finset.sum_neg_distrib]
    rw [bM_mul_aM, neg_add]
  | kk s t =>
    simp only [map_mul, map_add, map_zero, kMF, FreeAlgebra.lift_ι_apply, parityGenM, neg_mul_neg]
    rw [κM_mul_κM, neg_add_cancel]
  | kss s =>
    simp only [map_mul, map_zero, kMF, FreeAlgebra.lift_ι_apply, parityGenM, neg_mul_neg]
    exact κM_sq s
  | kb s u =>
    simp only [map_mul, kMF, bMF, FreeAlgebra.lift_ι_apply, parityGenM, neg_mul, mul_neg]
    rw [κM_mul_bM]
  | ka s i =>
    simp only [map_mul, map_add, map_zero, kMF, aMF, FreeAlgebra.lift_ι_apply, parityGenM,
      neg_mul_neg]
    rw [κM_mul_aM, neg_add_cancel]

/-- The grading automorphism: `b ↦ b`, `a ↦ −a`, `κ ↦ −κ`. -/
def parityM : SrcM J g β →ₐ[P] SrcM J g β := liftM parityGenM parityGenM_rel

theorem parityM_b (u : I) : parityM (bM J g β u) = bM J g β u := by
  simp only [parityM, bM, liftM_mk, bMF, FreeAlgebra.lift_ι_apply, parityGenM]
theorem parityM_a (i : K) : parityM (aM J g β i) = -aM J g β i := by
  simp only [parityM, aM, liftM_mk, aMF, FreeAlgebra.lift_ι_apply, parityGenM]
theorem parityM_κ (s : Fin r) : parityM (κM J g β s) = -κM J g β s := by
  simp only [parityM, κM, liftM_mk, kMF, FreeAlgebra.lift_ι_apply, parityGenM]

/-! ## Products of the `κ_s` -/

/-- The `P`-span of the products of `d` of the `κ_s`. -/
def kDeg (d : ℕ) : Submodule P (SrcM J g β) :=
  Submodule.span P {x | ∃ l : List (Fin r), l.length = d ∧ x = (l.map (κM J g β)).prod}

theorem kDeg_mul {d e : ℕ} {x y : SrcM J g β} (hx : x ∈ kDeg d) (hy : y ∈ kDeg e) :
    x * y ∈ kDeg (d + e) := by
  have h := Submodule.mul_mem_mul hx hy
  rw [kDeg, kDeg, Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨x, ⟨l1, hl1, rfl⟩, y, ⟨l2, hl2, rfl⟩, rfl⟩
  exact ⟨l1 ++ l2, by simp [hl1, hl2], by simp⟩

theorem κM_mem_kDeg (s : Fin r) : κM J g β s ∈ kDeg 1 :=
  Submodule.subset_span ⟨[s], rfl, by simp⟩

theorem κM_mul_prod_eq_zero (x : Fin r) (t : List (Fin r)) (h : x ∈ t) :
    κM J g β x * (t.map (κM J g β)).prod = 0 := by
  induction t with
  | nil => simp at h
  | cons y t ih =>
    rw [List.map_cons, List.prod_cons]
    by_cases hy : y = x
    · rw [hy, ← mul_assoc, κM_sq, zero_mul]
    · have hx : x ∈ t := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hy
        · exact h
      rw [← mul_assoc, κM_mul_κM, neg_mul, mul_assoc, ih hx, mul_zero, neg_zero]

theorem prod_eq_zero_of_not_nodup (l : List (Fin r)) (h : ¬ l.Nodup) :
    (l.map (κM J g β)).prod = 0 := by
  induction l with
  | nil => simp at h
  | cons x t ih =>
    rw [List.map_cons, List.prod_cons]
    by_cases hx : x ∈ t
    · exact κM_mul_prod_eq_zero x t hx
    · have ht : ¬ t.Nodup := fun ht => h (List.nodup_cons.mpr ⟨hx, ht⟩)
      rw [ih ht, mul_zero]

theorem kDeg_eq_bot {d : ℕ} (hd : r < d) : kDeg (J := J) (g := g) (β := β) d = ⊥ := by
  rw [kDeg, Submodule.span_eq_bot]
  rintro _ ⟨l, hl, rfl⟩
  apply prod_eq_zero_of_not_nodup
  intro hn
  have := hn.length_le_card
  simp only [Fintype.card_fin] at this
  omega

/-! ## `γ`, `c` and `Ω` -/

/-- `γ_{u,i} = Σ_s δ^{(s)}_{u,i} κ_s`. -/
def gammaM (δ : Fin r → I → K → P) (u : I) (i : K) : SrcM J g β := ∑ s, δ s u i • κM J g β s

variable (δ : Fin r → I → K → P)

theorem gammaM_mem_kDeg (u : I) (i : K) : gammaM (J := J) (g := g) (β := β) δ u i ∈ kDeg 1 :=
  Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (κM_mem_kDeg s)

theorem gammaM_mul_bM (u w : I) (i : K) :
    gammaM (J := J) (g := g) (β := β) δ u i * bM J g β w = bM J g β w * gammaM δ u i := by
  simp only [gammaM, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, κM_mul_bM]

theorem gammaM_mul_aM (u : I) (i j : K) :
    gammaM (J := J) (g := g) (β := β) δ u i * aM J g β j = -(aM J g β j * gammaM δ u i) := by
  simp only [gammaM, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, κM_mul_aM,
    smul_neg, Finset.sum_neg_distrib]

theorem gammaM_mul_κM (u : I) (i : K) (t : Fin r) :
    gammaM (J := J) (g := g) (β := β) δ u i * κM J g β t = -(κM J g β t * gammaM δ u i) := by
  simp only [gammaM, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [κM_mul_κM, smul_neg]

theorem κM_mul_gammaM (u : I) (i : K) (t : Fin r) :
    κM J g β t * gammaM (J := J) (g := g) (β := β) δ u i = -(gammaM δ u i * κM J g β t) := by
  rw [gammaM_mul_κM, neg_neg]

theorem gammaM_mul_gammaM (u v : I) (i j : K) :
    gammaM (J := J) (g := g) (β := β) δ u i * gammaM δ v j = -(gammaM δ v j * gammaM δ u i) := by
  change (∑ s, δ s u i • κM J g β s) * gammaM δ v j
    = -(gammaM δ v j * ∑ s, δ s u i • κM J g β s)
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_mul_assoc, κM_mul_gammaM, smul_neg, mul_smul_comm]

theorem gammaM_mul_gammaM_mem_center (v w : I) (i j : K) :
    gammaM (J := J) (g := g) (β := β) δ v i * gammaM δ w j
      ∈ Subalgebra.center P (SrcM J g β) := by
  apply mem_center_of_comm
  · intro u
    rw [mul_assoc, gammaM_mul_bM, ← mul_assoc, gammaM_mul_bM, mul_assoc]
  · intro k
    rw [mul_assoc, gammaM_mul_aM, mul_neg, ← mul_assoc, gammaM_mul_aM, neg_mul, neg_neg,
      mul_assoc]
  · intro t
    rw [mul_assoc, gammaM_mul_κM, mul_neg, ← mul_assoc, gammaM_mul_κM, neg_mul, neg_neg,
      mul_assoc]

/-- `γ_{x,j} a_j γ_{y,i} a_i = −γ_{x,j} γ_{y,i} a_j a_i`. -/
theorem gaga (x y : I) (i j : K) :
    gammaM (J := J) (g := g) (β := β) δ x j * aM J g β j * (gammaM δ y i * aM J g β i)
      = -(gammaM δ x j * gammaM δ y i * (aM J g β j * aM J g β i)) := by
  rw [mul_assoc, ← mul_assoc (aM J g β j), ← neg_neg (aM J g β j * gammaM δ y i),
    ← gammaM_mul_aM, neg_mul, mul_neg, mul_assoc, mul_assoc]

variable [Fintype K]

/-- `c_u = Σ_i γ_{u,i} a_i`. -/
def cM (u : I) : SrcM J g β := ∑ i, gammaM δ u i * aM J g β i

/-- `Ω_{uv} = [c_u, c_v]`, eq. (5.2). -/
def omegaM (u v : I) : SrcM J g β := cM (J := J) (g := g) (β := β) δ u * cM δ v - cM δ v * cM δ u

theorem cM_mul_aM (u : I) (j : K) :
    cM (J := J) (g := g) (β := β) δ u * aM J g β j
      = aM J g β j * cM δ u + ∑ s, (∑ i, δ s u i * g i j) • κM J g β s := by
  have h : cM (J := J) (g := g) (β := β) δ u * aM J g β j - aM J g β j * cM δ u
      = ∑ i, g i j • gammaM δ u i := by
    simp only [cM, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc (aM J g β j), ← neg_neg (aM J g β j * gammaM δ u i), ← gammaM_mul_aM,
      neg_mul, sub_neg_eq_add, mul_assoc, mul_assoc, ← mul_add, aM_mul_aM_add,
      ← Algebra.commutes, Algebra.smul_def]
  rw [← sub_eq_iff_eq_add', h]
  simp only [gammaM, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]

theorem bM_mul_cM_zero (u v : I) :
    bM J g 0 u * cM (J := J) (g := g) δ v = cM δ v * bM J g 0 u := by
  simp only [cM, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, ← gammaM_mul_bM, mul_assoc, bM_mul_aM, mul_add, mul_assoc]
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, mul_zero, add_zero]

theorem omegaM_antisymm (u v : I) :
    omegaM (J := J) (g := g) (β := β) δ v u = -omegaM δ u v := by
  simp only [omegaM, neg_sub]

/-- `Ω_{wv} = Σ_{i,j} g_{ji} γ_{v,i} γ_{w,j}`. -/
theorem omegaM_eq (w v : I) :
    omegaM (J := J) (g := g) (β := β) δ w v
      = ∑ i, ∑ j, g j i • (gammaM δ v i * gammaM δ w j) := by
  have h1 : cM (J := J) (g := g) (β := β) δ w * cM δ v
      = ∑ i, ∑ j, -(gammaM δ w j * gammaM δ v i * (aM J g β j * aM J g β i)) := by
    rw [cM, cM, Finset.sum_mul_sum, Finset.sum_comm]
    simp only [gaga]
  have h2 : cM (J := J) (g := g) (β := β) δ v * cM δ w
      = ∑ i, ∑ j, gammaM δ w j * gammaM δ v i * (aM J g β i * aM J g β j) := by
    rw [cM, cM, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [gaga, gammaM_mul_gammaM δ v w i j, neg_mul, neg_neg]
  rw [omegaM, h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gammaM_mul_gammaM δ v w i j, smul_neg, sub_eq_add_neg, ← neg_add, ← mul_add, aM_mul_aM_add,
    ← Algebra.commutes, Algebra.smul_def]

theorem omegaM_mem_center (u v : I) :
    omegaM (J := J) (g := g) (β := β) δ u v ∈ Subalgebra.center P (SrcM J g β) := by
  rw [omegaM_eq]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ =>
    Subalgebra.smul_mem _ (gammaM_mul_gammaM_mem_center δ v u i j) _

theorem omegaM_mem_kDeg (u v : I) : omegaM (J := J) (g := g) (β := β) δ u v ∈ kDeg 2 := by
  rw [omegaM_eq]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
  have h := kDeg_mul (gammaM_mem_kDeg (J := J) (g := g) (β := β) δ v i) (gammaM_mem_kDeg δ u j)
  rwa [show (1 : ℕ) + 1 = 2 from rfl] at h

/-- `[b_w, c_v] = Ω_{wv}` in `A_β`, when `Σ_i δ^{(s)}_{u,i} g_{ji} = β^{(s)}_{u,j}` and `g` is
symmetric. -/
theorem bM_mul_cM (hg : ∀ i j, g i j = g j i)
    (hδ : ∀ s u j, ∑ i, δ s u i * g j i = β s u j) (w v : I) :
    bM J g β w * cM δ v = cM δ v * bM J g β w + omegaM δ w v := by
  have hγβ : ∀ i, (∑ s, β s w i • κM J g β s) = ∑ j, g j i • gammaM (J := J) (g := g) δ w j := by
    intro i
    simp only [gammaM, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← hδ s w i, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg i j, mul_comm]
  have h : bM J g β w * cM δ v
      = cM δ v * bM J g β w + ∑ i, gammaM δ v i * (∑ s, β s w i • κM J g β s) := by
    simp only [cM, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, ← gammaM_mul_bM, mul_assoc, bM_mul_aM, mul_add, mul_assoc, Finset.mul_sum]
  rw [h, omegaM_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hγβ i, Finset.mul_sum]
  simp only [mul_smul_comm]

end Presented
end OspN
end OspOddDeformations
