import OspOddDeformations.OspN.Gamma
import OspOddDeformations.OspN.Laws
import Mathlib.Tactic.Module

/-!
# `Γ_β = δh̃`, for every `osp(N|2n)`

The identity `Γ_β = δh̃` on `𝔤_P`, with `Γ_β` given by paper Proposition 4.4 and `h̃` by
Proposition 4.1, for a general `FermionIndex`. Every step uses only `F.dual_dual`,
`F.g_symm`/`g_eq_dual`, and `F.key_injective`, never the concrete shape of the fermion index
(for odd `N`, `Option (Fin m × Bool)`). The injectivity of the sort key, whose proof for odd `N`
(`Bmn.KKey_injective`) does pattern-match on `none`/`some`, is a field of `FermionIndex`
(`F.key_injective`), supplied per instance.

Proved sector by sector (`LL`/`SS` free — both sides vanish; `LF`, `LS`,
`SF` by direct computation; `FL`, `SL`, `FS` from those by the reversal
shortcut `deltaBasis_hTilde_swap`, itself derived from
`bracket0Basis_super_skew` (`Laws.lean`) plus `hTilde`'s oddness; `FF` by
direct computation), then assembled into the nine-case basis-level match
and extended bilinearly (`Gamma_eq_delta_hTilde`), for every `FermionIndex`, not just
`oddIdx`/`evenIdx`.
-/

-- Toolchain port (v4.34): `OspBasis` is a plain `def` whose sum structure the proofs use; restore
-- the pre-v4.34 type-transparency behaviour of `isDefEq` for this file.
set_option backward.isDefEq.respectTransparency.types false


namespace OspOddDeformations
namespace OspN

open Bmn (I J IKey J_antisymm)

theorem hTilde_eN {F : FermionIndex} {n : ℕ} (X : OspBasis F n) : hTilde (eN X) =
  hTildeBasis X := by
  unfold hTilde
  rw [Finset.sum_eq_single X]
  · simp [eN]
  · intro b _ hb; simp [eN, hb]
  · intro h; exact absurd (Finset.mem_univ X) h

theorem bracket0_eN_eN {F : FermionIndex} {n : ℕ} (X Y : OspBasis F n) :
    bracket0 (eN X) (eN Y) = bracket0Basis X Y := by
  unfold bracket0
  funext k
  rw [Finset.sum_apply k Finset.univ]
  rw [Finset.sum_eq_single X]
  · rw [Finset.sum_apply k Finset.univ]
    rw [Finset.sum_eq_single Y]
    · simp [eN]
    · intro b _ hb; simp [eN, hb]
    · intro h; exact absurd (Finset.mem_univ Y) h
  · intro b _ hb
    rw [Finset.sum_apply k Finset.univ]
    apply Finset.sum_eq_zero
    intro j _
    simp [eN, hb]
  · intro h; exact absurd (Finset.mem_univ X) h

theorem bracket0_eN_left {F : FermionIndex} {n : ℕ} (X : OspBasis F n) (y : OspMod F n) :
    bracket0 (eN X) y = ∑ j : OspBasis F n, y j • bracket0Basis X j := by
  unfold bracket0
  rw [Finset.sum_eq_single X]
  · apply Finset.sum_congr rfl
    intro j _
    simp [eN]
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro j _
    simp [eN, hb]
  · intro h; exact absurd (Finset.mem_univ X) h

theorem bracket0_eN_right {F : FermionIndex} {n : ℕ} (x : OspMod F n) (Y : OspBasis F n) :
    bracket0 x (eN Y) = ∑ i : OspBasis F n, x i • bracket0Basis i Y := by
  unfold bracket0
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single Y]
  · simp [eN]
  · intro b _ hb; simp [eN, hb]
  · intro h; exact absurd (Finset.mem_univ Y) h

theorem bracket0_sum_left {F : FermionIndex} {n : ℕ} {α : Type*} (s : Finset α) (f : α → OspMod F n)
    (y : OspMod F n) :
    bracket0 (∑ a ∈ s, f a) y = ∑ a ∈ s, bracket0 (f a) y := by
  unfold bracket0
  funext k
  rw [Finset.sum_apply k s]
  simp only [Finset.sum_apply, ospMod_smul_apply, Finset.sum_mul]
  rw [show (∑ x : OspBasis F n, ∑ x1 : OspBasis F n, ∑ i ∈ s, f i x * y x1 * bracket0Basis x x1 k)
      = ∑ x : OspBasis F n, ∑ i ∈ s, ∑ x1 : OspBasis F n, f i x * y x1 * bracket0Basis x x1 k from
        Finset.sum_congr rfl (fun x _ => Finset.sum_comm)]
  rw [Finset.sum_comm]

theorem bracket0_smul_left {F : FermionIndex} {n : ℕ} (c : Pmn F n) (x y : OspMod F n) :
    bracket0 (c • x) y = c • bracket0 x y := by
  unfold bracket0
  funext k
  simp only [Finset.sum_apply, ospMod_smul_apply]
  rw [Finset.mul_sum]
  congr 1
  funext i
  rw [Finset.mul_sum]
  congr 1
  funext j
  ring

theorem bracket0_sum_right {F : FermionIndex} {n : ℕ} {α : Type*} (s : Finset α) (x : OspMod F n)
    (f : α → OspMod F n) :
    bracket0 x (∑ a ∈ s, f a) = ∑ a ∈ s, bracket0 x (f a) := by
  unfold bracket0
  funext k
  rw [Finset.sum_apply k s]
  simp only [Finset.sum_apply, ospMod_smul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [show (∑ x1 : OspBasis F n, ∑ x2 : OspBasis F n, ∑ i ∈ s,
        x x1 * f i x2 * bracket0Basis x1 x2 k)
      = ∑ x1 : OspBasis F n, ∑ i ∈ s, ∑ x2 : OspBasis F n,
        x x1 * f i x2 * bracket0Basis x1 x2 k from
        Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm)]
  rw [Finset.sum_comm]

theorem bracket0_smul_right {F : FermionIndex} {n : ℕ} (c : Pmn F n) (x y : OspMod F n) :
    bracket0 x (c • y) = c • bracket0 x y := by
  unfold bracket0
  funext k
  simp only [Finset.sum_apply, ospMod_smul_apply]
  rw [Finset.mul_sum]
  congr 1
  funext i
  rw [Finset.mul_sum]
  congr 1
  funext j
  ring

theorem hTilde_add {F : FermionIndex} {n : ℕ} (x y : OspMod F n) : hTilde (x + y) = hTilde x
  + hTilde y := by
  unfold hTilde
  funext k
  simp only [Finset.sum_apply, ospMod_add_apply, ospMod_smul_apply, add_mul,
    Finset.sum_add_distrib]

theorem hTilde_smul {F : FermionIndex} {n : ℕ} (c : Pmn F n) (x : OspMod F n) :
    hTilde (c • x) = c • hTilde x := by
  unfold hTilde
  funext k
  simp only [Finset.sum_apply, ospMod_smul_apply, Finset.mul_sum, mul_assoc]

theorem hTilde_smul_rat {F : FermionIndex} {n : ℕ} (c : ℚ) (x : OspMod F n) :
    hTilde (c • x) = c • hTilde x := by
  unfold hTilde
  funext k
  simp [Finset.smul_sum]

theorem qsmul_eq_Csmul {F : FermionIndex} {n : ℕ} (c : ℚ) (v : OspMod F n) :
    c • v = (MvPolynomial.C c : Pmn F n) • v := by
  funext k
  simp [Algebra.smul_def]

theorem dual_bijective {F : FermionIndex} : Function.Bijective (F.dual) :=
  Function.Involutive.bijective F.dual_dual

theorem sum_dual {F : FermionIndex} {M : Type*} [AddCommMonoid M] (f : F.K → M) :
    ∑ i : F.K, f (F.dual i) = ∑ i : F.K, f i :=
  dual_bijective.sum_comp f

theorem g_eq_dual {F : FermionIndex} (i k : F.K) : F.g i k = if i = F.dual k then 1 else 0 := by
  unfold FermionIndex.g
  by_cases h : k = F.dual i
  · subst h; simp [F.dual_dual]
  · have h2 : i ≠ F.dual k := fun he => h (by rw [he, F.dual_dual])
    simp [h, h2]

theorem sum_beta_dual_Sof {F : FermionIndex} {n : ℕ} (a : I n) (kk : F.K) :
    (∑ x : F.K, beta F n a (F.dual x) • Sof x kk : OspMod F n) =
      ∑ x : F.K, beta F n a x • Sof (F.dual x) kk := by
  have h := sum_dual (M := OspMod F n) (fun x => beta F n a x • Sof (F.dual x) kk)
  simp only [F.dual_dual] at h
  exact h

theorem hTildeBasis_inl {F : FermionIndex} {n : ℕ} (u v : I n) (h : IKey u ≤ IKey v) :
    hTildeBasis (Sum.inl ⟨(u, v), h⟩ : OspBasis F n) =
      ∑ i : F.K, (beta F n u (F.dual i) • eN (Fof v i) + beta F n v (F.dual i) • eN (Fof u i)) :=
  rfl

theorem hTildeBasis_Lof {F : FermionIndex} {n : ℕ} (u z : I n) :
    hTildeBasis (Lof u z : OspBasis F n) =
      ∑ i : F.K, (beta F n u (F.dual i) • eN (Fof z i) + beta F n z (F.dual i) • eN (Fof u i)) := by
  unfold Lof
  split
  · rfl
  · simp only [hTildeBasis]
    apply Finset.sum_congr rfl
    intro i _
    rw [add_comm]

theorem hTilde_neg {F : FermionIndex} {n : ℕ} (x : OspMod F n) : hTilde (-x) = -hTilde x := by
  unfold hTilde
  funext k
  simp only [Finset.sum_apply, ospMod_neg_apply, neg_smul, Finset.sum_neg_distrib]

theorem hTilde_zero {F : FermionIndex} {n : ℕ} : hTilde (0 : OspMod F n) = 0 := by
  unfold hTilde
  funext k
  simp

theorem hTilde_Sof {F : FermionIndex} {n : ℕ} (i j : F.K) : hTilde (Sof i j : OspMod F n) = 0 := by
  unfold Sof
  split
  · rw [hTilde_eN]; simp [hTildeBasis]
  · split
    · rw [hTilde_neg, hTilde_eN]; simp [hTildeBasis]
    · exact hTilde_zero

theorem bracket0_zero_left {F : FermionIndex} {n : ℕ} (y : OspMod F n) : bracket0
  (0 : OspMod F n) y = 0 := by
  unfold bracket0
  funext k
  simp

theorem bracket0_zero_right {F : FermionIndex} {n : ℕ} (x : OspMod F n) : bracket0 x
  (0 : OspMod F n) = 0 := by
  unfold bracket0
  funext k
  simp

theorem bracket0_add_left {F : FermionIndex} {n : ℕ} (x y z : OspMod F n) :
    bracket0 (x + y) z = bracket0 x z + bracket0 y z := by
  unfold bracket0
  funext k
  simp only [Finset.sum_apply, ospMod_add_apply, ospMod_smul_apply, add_mul,
    Finset.sum_add_distrib]

theorem bracket0_add_right {F : FermionIndex} {n : ℕ} (x y z : OspMod F n) :
    bracket0 x (y + z) = bracket0 x y + bracket0 x z := by
  unfold bracket0
  funext k
  simp only [Finset.sum_apply, ospMod_add_apply, ospMod_smul_apply, mul_add, add_mul,
    Finset.sum_add_distrib]

theorem hTildeBasis_Fof {F : FermionIndex} {n : ℕ} (u : I n) (i : F.K) :
    hTildeBasis (Fof u i : OspBasis F n) =
      (1 / 2 : ℚ) • ∑ j : F.K, beta F n u j • Sof (F.dual j) i :=
  rfl

theorem bracket0_neg_right {F : FermionIndex} {n : ℕ} (x y : OspMod F n) : bracket0 x (-y) =
  -bracket0 x y := by
  unfold bracket0
  funext k
  simp only [Finset.sum_apply, ospMod_neg_apply, ospMod_smul_apply, mul_neg, neg_mul,
    Finset.sum_neg_distrib]

theorem bracket0_neg_left {F : FermionIndex} {n : ℕ} (x y : OspMod F n) : bracket0 (-x) y =
  -bracket0 x y := by
  unfold bracket0
  funext k
  simp only [Finset.sum_apply, ospMod_neg_apply, ospMod_smul_apply, neg_mul,
    Finset.sum_neg_distrib]

theorem bracket0_smul_right_rat {F : FermionIndex} {n : ℕ} (c : ℚ) (x y : OspMod F n) :
    bracket0 x (c • y) = c • bracket0 x y := by
  unfold bracket0
  funext k
  simp [Finset.smul_sum]

theorem bracket0_smul_left_rat {F : FermionIndex} {n : ℕ} (c : ℚ) (x y : OspMod F n) :
    bracket0 (c • x) y = c • bracket0 x y := by
  unfold bracket0
  funext k
  simp [Finset.smul_sum]

theorem bracket0_L_Sof {F : FermionIndex} {n : ℕ} (u v : I n) (hp : IKey u ≤ IKey v) (a b : F.K) :
    bracket0 (eN (Sum.inl ⟨(u, v), hp⟩) : OspMod F n) (Sof a b) = 0 := by
  unfold Sof
  split
  · rw [bracket0_eN_eN]; rfl
  · split
    · rw [bracket0_neg_right, bracket0_eN_eN]; simp [bracket0Basis]
    · exact bracket0_zero_right _

/-! ## `SS` sector — free (both sides vanish) -/

theorem delta_hTilde_SS {F : FermionIndex} {n : ℕ} (i j k l : F.K) (hij : F.key i < F.key j)
  (hkl : F.key k < F.key l) :
    deltaBasis hTilde (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n)
      (Sum.inr (Sum.inl ⟨(k, l), hkl⟩)) = 0 := by
  unfold deltaBasis
  have hX : hTilde (eN (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n)) = 0 := by
    rw [hTilde_eN]; rfl
  have hY : hTilde (eN (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n)) = 0 := by
    rw [hTilde_eN]; rfl
  rw [hX, hY, bracket0_zero_left, bracket0_zero_right, smul_zero, zero_add, bracket0_eN_eN]
  simp only [bracket0Basis]
  unfold bracketSS
  simp [sub_eq_add_neg, hTilde_add, hTilde_neg, hTilde_smul_rat, hTilde_Sof]

/-! ## `LF` sector — direct computation -/

theorem delta_hTilde_LF {F : FermionIndex} {n : ℕ} (u v w : I n) (kk : F.K) (hp : IKey u ≤ IKey v) :
    deltaBasis hTilde (Sum.inl ⟨(u, v), hp⟩ : OspBasis F n) (Fof w kk) = GammaLF u v w kk := by
  unfold deltaBasis
  have hterm2 : bracket0 (eN (Sum.inl ⟨(u, v), hp⟩) : OspMod F n) (hTilde (eN (Fof w kk))) = 0 := by
    rw [hTilde_eN, hTildeBasis_Fof, bracket0_smul_right_rat, bracket0_sum_right]
    simp only [bracket0_smul_right, bracket0_L_Sof, smul_zero, Finset.sum_const_zero]
  rw [hterm2, smul_zero, add_zero]
  simp only [hTilde_eN, bracket0_eN_eN, bracket0Basis, Fof,
    bracket0_sum_left, bracket0_add_left, bracket0_smul_left, bracketFF, bracketLF, GammaLF,
    hTilde_add, hTilde_smul_rat, hTildeBasis, smul_add, Finset.sum_add_distrib,
    Finset.smul_sum]
  rw [show (∑ x : F.K, beta F n u (F.dual x) • (1 / 2 * F.g x kk) • eN (Lof v w) : OspMod F n)
      = beta F n u kk • (1 / 2 : ℚ) • eN (Lof v w) from by
        rw [Finset.sum_eq_single (F.dual kk)]
        · rw [g_eq_dual]; simp [F.dual_dual]
        · intro b _ hb; rw [g_eq_dual]; simp [hb]
        · intro h; exact absurd (Finset.mem_univ _) h,
      show (∑ x : F.K, beta F n v (F.dual x) • (1 / 2 * F.g x kk) • eN (Lof u w) : OspMod F n)
      = beta F n v kk • (1 / 2 : ℚ) • eN (Lof u w) from by
        rw [Finset.sum_eq_single (F.dual kk)]
        · rw [g_eq_dual]; simp [F.dual_dual]
        · intro b _ hb; rw [g_eq_dual]; simp [hb]
        · intro h; exact absurd (Finset.mem_univ _) h]
  have hu3 : (∑ x : F.K, beta F n u (F.dual x) • (1 / 4 * J n v w) • Sof x kk : OspMod F n)
      = ∑ x : F.K, (1 / 2 * J n v w) • (1 / 2 : ℚ) • beta F n u x • Sof (F.dual x) kk := by
    rw [show (∑ x : F.K, beta F n u (F.dual x) • (1 / 4 * J n v w) • Sof x kk : OspMod F n)
        = (1 / 4 * J n v w : ℚ) • ∑ x : F.K, beta F n u (F.dual x) • Sof x kk from by
          rw [Finset.smul_sum]; exact Finset.sum_congr rfl (fun x _ => smul_comm _ _ _)]
    rw [sum_beta_dual_Sof, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [smul_smul]
    congr 1
    ring
  have hv3 : (∑ x : F.K, beta F n v (F.dual x) • (1 / 4 * J n u w) • Sof x kk : OspMod F n)
      = ∑ x : F.K, (1 / 2 * J n u w) • (1 / 2 : ℚ) • beta F n v x • Sof (F.dual x) kk := by
    rw [show (∑ x : F.K, beta F n v (F.dual x) • (1 / 4 * J n u w) • Sof x kk : OspMod F n)
        = (1 / 4 * J n u w : ℚ) • ∑ x : F.K, beta F n v (F.dual x) • Sof x kk from by
          rw [Finset.smul_sum]; exact Finset.sum_congr rfl (fun x _ => smul_comm _ _ _)]
    rw [sum_beta_dual_Sof, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [smul_smul]
    congr 1
    ring
  rw [hu3, hv3, smul_comm (beta F n u kk) (1 / 2 : ℚ), smul_comm (beta F n v kk) (1 / 2 : ℚ)]
  abel

/-! ## `LL` sector — free (both sides vanish) -/

theorem delta_hTilde_LL {F : FermionIndex} {n : ℕ} (u v w z : I n) (hp : IKey u ≤ IKey v)
  (hq : IKey w ≤ IKey z) :
    deltaBasis hTilde (Sum.inl ⟨(u, v), hp⟩ : OspBasis F n) (Sum.inl ⟨(w, z), hq⟩) = 0 := by
  unfold deltaBasis
  simp only [hTilde_eN, parity, gsign, hTildeBasis_inl, Fof,
    bracket0_sum_left, bracket0_sum_right, bracket0_add_left, bracket0_add_right,
    bracket0_smul_left, bracket0_smul_right, bracket0_eN_eN, bracket0Basis,
    hTilde_add, hTilde_smul_rat, bracketLL, bracketLF, hTildeBasis_Lof,
    show ((0 : ZMod 2) = 1) = False from by simp, false_and, ite_false]
  simp only [one_smul, Finset.smul_sum, smul_add, smul_neg, sub_eq_add_neg,
    ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro x _
  rw [J_antisymm z v, J_antisymm z u, J_antisymm w v, J_antisymm w u]
  funext k
  simp [eN]
  abel

/-! ## The reversal shortcut

`deltaBasis hTilde` obeys the same super-skew law as `bracket0Basis`
itself, for *every* ordered basis pair: `deltaBasis hTilde Y X =
-(gsign (parity X) (parity Y)) • deltaBasis hTilde X Y`. Derived purely
from `bracket0Basis_super_skew` (`Laws.lean`) plus `hTilde`'s oddness (it
shifts parity by `1`); no sector-specific computation. Used to get `FL`
from `LF`, `SL` from `LS`, `FS` from `SF`, each a one-line corollary. -/

/-- `hTildeBasis X` is homogeneous of parity `parity X + 1`: any basis point
`Z` where it is nonzero must have the shifted parity. Needed to run
`bracket0`'s super-skew law against `hTilde (eN X)`, which is a sum of basis
vectors but not itself a single basis vector. -/
theorem hTildeBasis_apply_eq_zero_of_parity_ne {F : FermionIndex} {n : ℕ} (X Z : OspBasis F n)
    (h : parity Z ≠ parity X + 1) : hTildeBasis X Z = 0 := by
  match X with
  | .inl ⟨(u, v), hp⟩ =>
    match Z with
    | .inl _ =>
      rw [hTildeBasis_inl]
      simp [Finset.sum_apply]
    | .inr (.inl _) =>
      rw [hTildeBasis_inl]
      simp [Finset.sum_apply]
    | .inr (.inr _) => simp [parity] at h
  | .inr (.inl _) => simp [hTildeBasis]
  | .inr (.inr (u, i)) =>
    match Z with
    | .inl _ => exact absurd (by simp only [parity]; decide) h
    | .inr (.inl _) => exact absurd (by simp only [parity]; decide) h
    | .inr (.inr (w, q)) =>
      rw [show (Sum.inr (Sum.inr (u, i)) : OspBasis F n) = Fof u i from rfl, hTildeBasis_Fof]
      simp [Finset.sum_apply, Sof_apply_inrF]

/-- `hTilde (eN X)` is homogeneous of parity `parity X + 1` — the
"`hTilde`'s oddness" fact the reversal shortcut needs. -/
theorem hTilde_eN_apply_eq_zero_of_parity_ne {F : FermionIndex} {n : ℕ} (X Z : OspBasis F n)
    (h : parity Z ≠ parity X + 1) : hTilde (eN X) Z = 0 := by
  rw [hTilde_eN]; exact hTildeBasis_apply_eq_zero_of_parity_ne X Z h

/-- `bracket0` super-skew against a homogeneous element `x` (of parity `p`,
witnessed by `hx`) and a single basis vector `eN Y`: the same sign rule as
`bracket0Basis_super_skew`, extended off the basis. -/
theorem bracket0_homog_swap {F : FermionIndex} {n : ℕ} (p : ZMod 2) (x : OspMod F n)
    (hx : ∀ Z : OspBasis F n, x Z ≠ 0 → parity Z = p) (Y : OspBasis F n) :
    bracket0 x (eN Y) = -(gsign p (parity Y)) • bracket0 (eN Y) x := by
  rw [bracket0_eN_right, bracket0_eN_left, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hxi : x i = 0
  · simp [hxi]
  · rw [bracket0Basis_super_skew i Y, hx i hxi]
    exact smul_comm (x i) (-gsign p (parity Y)) (bracket0Basis Y i)

/-- Mirror of `bracket0_homog_swap`, with the basis vector on the left
instead of the right. -/
theorem bracket0_swap_homog {F : FermionIndex} {n : ℕ} (p : ZMod 2) (x : OspMod F n)
    (hx : ∀ Z : OspBasis F n, x Z ≠ 0 → parity Z = p) (Y : OspBasis F n) :
    bracket0 (eN Y) x = -(gsign (parity Y) p) • bracket0 x (eN Y) := by
  rw [bracket0_eN_left, bracket0_eN_right, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hxi : x i = 0
  · simp [hxi]
  · rw [bracket0Basis_super_skew Y i, hx i hxi]
    exact smul_comm (x i) (-gsign (parity Y) p) (bracket0Basis i Y)

theorem gsign_symm (p q : ZMod 2) : gsign p q = gsign q p := by
  fin_cases p <;> fin_cases q <;> decide

/-- General gsign identity (G1): needed to match the `hTilde(bracket0)`
coefficient in `deltaBasis_hTilde_swap`. -/
theorem gsign_mul_shift_right (p q : ZMod 2) : gsign q 1 * gsign q (p + 1) = gsign p q := by
  fin_cases p <;> fin_cases q <;>
    simp only [gsign, Fin.isValue, Fin.mk_one, Fin.zero_eta, Nat.reduceAdd, add_eq_right, and_self,
      and_true, mul_ite, mul_neg, mul_one] <;> decide

/-- General gsign identity (G2): needed to match the `bracket0 (eN X)
(hTilde (eN Y))` coefficient in `deltaBasis_hTilde_swap`. -/
theorem gsign_shift_right (p q : ZMod 2) : gsign p (q + 1) = gsign p q * gsign p 1 := by
  fin_cases p <;> fin_cases q <;>
    simp only [gsign, Fin.isValue, Fin.mk_one, Fin.zero_eta, Nat.reduceAdd, add_eq_right, and_self,
      and_true, mul_ite, mul_neg, mul_one] <;> decide

/-- **The reversal shortcut**: `deltaBasis hTilde` obeys the same
super-skew law as `bracket0Basis` itself, for *every* ordered basis pair —
not just the three sectors it is used for below. Derived purely from
`bracket0Basis_super_skew` plus `hTilde`'s oddness
(`hTilde_eN_apply_eq_zero_of_parity_ne`); no sector-specific computation. -/
theorem deltaBasis_hTilde_swap {F : FermionIndex} {n : ℕ} (X Y : OspBasis F n) :
    deltaBasis hTilde Y X = -(gsign (parity X) (parity Y)) • deltaBasis hTilde X Y := by
  have hX : ∀ Z : OspBasis F n, hTilde (eN X) Z ≠ 0 → parity Z = parity X + 1 :=
    fun Z hZ => by
      by_contra hne; exact hZ (hTilde_eN_apply_eq_zero_of_parity_ne X Z hne)
  have hY : ∀ Z : OspBasis F n, hTilde (eN Y) Z ≠ 0 → parity Z = parity Y + 1 :=
    fun Z hZ => by
      by_contra hne; exact hZ (hTilde_eN_apply_eq_zero_of_parity_ne Y Z hne)
  have hA : bracket0 (hTilde (eN Y)) (eN X) =
      -(gsign (parity Y + 1) (parity X)) • bracket0 (eN X) (hTilde (eN Y)) :=
    bracket0_homog_swap (parity Y + 1) (hTilde (eN Y)) hY X
  have hB : bracket0 (eN Y) (hTilde (eN X)) =
      -(gsign (parity Y) (parity X + 1)) • bracket0 (hTilde (eN X)) (eN Y) :=
    bracket0_swap_homog (parity X + 1) (hTilde (eN X)) hX Y
  have hC : bracket0 (eN Y) (eN X) =
      -(gsign (parity Y) (parity X)) • bracket0 (eN X) (eN Y) := by
    rw [bracket0_eN_eN, bracket0_eN_eN, bracket0Basis_super_skew Y X]
  unfold deltaBasis
  rw [hA, hB, hC]
  rw [show hTilde (-(gsign (parity Y) (parity X)) • bracket0 (eN X) (eN Y))
      = -(gsign (parity Y) (parity X)) • hTilde (bracket0 (eN X) (eN Y)) from
        hTilde_smul_rat _ _]
  simp only [smul_smul, smul_neg, neg_smul]
  rw [show gsign (parity Y + 1) (parity X) = gsign (parity X) (parity Y + 1) from
        gsign_symm _ _,
      gsign_shift_right (parity X) (parity Y),
      gsign_mul_shift_right (parity X) (parity Y),
      show gsign (parity Y) (parity X) = gsign (parity X) (parity Y) from gsign_symm _ _]
  module

/-! ## `LS` sector — direct computation (the real content is on the `Γ`
side; `bracket0Basis`'s `LS` case is literally `0`, so this is not the
free "both sides vanish" pattern `SS`/`LL` were). -/

theorem delta_hTilde_LS {F : FermionIndex} {n : ℕ} (u v : I n) (i j : F.K) (hp : IKey u ≤ IKey v)
    (hij : F.key i < F.key j) :
    deltaBasis hTilde (Sum.inl ⟨(u, v), hp⟩ : OspBasis F n)
      (Sum.inr (Sum.inl ⟨(i, j), hij⟩)) = GammaLS u v i j := by
  unfold deltaBasis
  have hterm2 : bracket0 (eN (Sum.inl ⟨(u, v), hp⟩) : OspMod F n)
      (hTilde (eN (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n))) = 0 := by
    rw [hTilde_eN]; simp only [hTildeBasis]; exact bracket0_zero_right _
  have hterm3 : (bracket0 (eN (Sum.inl ⟨(u, v), hp⟩) : OspMod F n)
      (eN (Sum.inr (Sum.inl ⟨(i, j), hij⟩)))) = 0 := by
    rw [bracket0_eN_eN]; rfl
  rw [hterm2, smul_zero, add_zero, hterm3, hTilde_zero, sub_zero]
  simp only [hTilde_eN, hTildeBasis_inl, Fof,
    bracket0_sum_left, bracket0_add_left, bracket0_smul_left,
    bracket0_eN_eN, bracket0Basis, bracketSF, GammaLS]
  simp only [smul_sub, neg_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [show (∑ x : F.K, beta F n u (F.dual x) • F.g i x •
        eN (Sum.inr (Sum.inr (v, j)) : OspBasis F n))
      = beta F n u i • eN (Sum.inr (Sum.inr (v, j)) : OspBasis F n) from by
        rw [Finset.sum_eq_single (F.dual i)]
        · rw [g_eq_dual]; simp [F.dual_dual]
        · intro b _ hb
          rw [g_eq_dual]
          have : i ≠ F.dual b := fun he => hb (by rw [he, F.dual_dual])
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h,
      show (∑ x : F.K, beta F n u (F.dual x) • F.g j x •
        eN (Sum.inr (Sum.inr (v, i)) : OspBasis F n))
      = beta F n u j • eN (Sum.inr (Sum.inr (v, i)) : OspBasis F n) from by
        rw [Finset.sum_eq_single (F.dual j)]
        · rw [g_eq_dual]; simp [F.dual_dual]
        · intro b _ hb
          rw [g_eq_dual]
          have : j ≠ F.dual b := fun he => hb (by rw [he, F.dual_dual])
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h,
      show (∑ x : F.K, beta F n v (F.dual x) • F.g i x •
        eN (Sum.inr (Sum.inr (u, j)) : OspBasis F n))
      = beta F n v i • eN (Sum.inr (Sum.inr (u, j)) : OspBasis F n) from by
        rw [Finset.sum_eq_single (F.dual i)]
        · rw [g_eq_dual]; simp [F.dual_dual]
        · intro b _ hb
          rw [g_eq_dual]
          have : i ≠ F.dual b := fun he => hb (by rw [he, F.dual_dual])
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h,
      show (∑ x : F.K, beta F n v (F.dual x) • F.g j x •
        eN (Sum.inr (Sum.inr (u, i)) : OspBasis F n))
      = beta F n v j • eN (Sum.inr (Sum.inr (u, i)) : OspBasis F n) from by
        rw [Finset.sum_eq_single (F.dual j)]
        · rw [g_eq_dual]; simp [F.dual_dual]
        · intro b _ hb
          rw [g_eq_dual]
          have : j ≠ F.dual b := fun he => hb (by rw [he, F.dual_dual])
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h]
  abel

/-- **FL**, derived from **LF** by the reversal shortcut
(`deltaBasis_hTilde_swap`): `p(L) = 0`, `p(F) = 1`, `gsign 0 1 = 1`, so the
sign is just `-1`. -/
theorem delta_hTilde_FL {F : FermionIndex} {n : ℕ} (u v w : I n) (kk : F.K) (hp : IKey u ≤ IKey v) :
    deltaBasis hTilde (Fof w kk : OspBasis F n) (Sum.inl ⟨(u, v), hp⟩) = -GammaLF u v w kk := by
  rw [deltaBasis_hTilde_swap (Sum.inl ⟨(u, v), hp⟩) (Fof w kk), delta_hTilde_LF]
  simp [parity, Fof, gsign]

/-- **SL**, derived from **LS** by the reversal shortcut: `p(L) = p(S) = 0`,
`gsign 0 0 = 1`, so again sign `-1`. -/
theorem delta_hTilde_SL {F : FermionIndex} {n : ℕ} (u v : I n) (i j : F.K) (hp : IKey u ≤ IKey v)
    (hij : F.key i < F.key j) :
    deltaBasis hTilde (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n)
      (Sum.inl ⟨(u, v), hp⟩) = -GammaLS u v i j := by
  rw [deltaBasis_hTilde_swap (Sum.inl ⟨(u, v), hp⟩) (Sum.inr (Sum.inl ⟨(i, j), hij⟩)),
    delta_hTilde_LS]
  simp [parity, gsign]


/-- `bracketSS` is antisymmetric in its last two arguments, as a pure
algebraic identity in the formula itself (no ordering hypothesis needed):
the four terms of `bracketSS i j l k` are exactly `bracketSS i j k l`'s
four terms, permuted. -/
theorem bracketSS_swap34 {F : FermionIndex} {n : ℕ} (i j k l : F.K) :
    (bracketSS i j k l : OspMod F n) = -bracketSS i j l k := by
  unfold bracketSS
  abel

/-- `bracketSS` vanishes when its last two arguments coincide. -/
theorem bracketSS_diag {F : FermionIndex} {n : ℕ} (i j a : F.K) :
  (bracketSS i j a a : OspMod F n) = 0 := by
  unfold bracketSS
  abel

/-- `bracket0` against an `S`-basis vector, on the other side matched with
an arbitrary (not necessarily sorted) `Sof a b`, always reduces to
`bracketSS i j a b` — the `S`-kind analogue of `bracket0_L_Sof` (which is
always `0`). Needed because `hTildeBasis_Fof`'s sum ranges over all `l : K
m`, not just the sorted ones. -/
theorem bracket0_S_Sof {F : FermionIndex} {n : ℕ} (i j : F.K)
  (hij : F.key i < F.key j) (a b : F.K) :
    bracket0 (eN (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n)) (Sof a b) =
      bracketSS i j a b := by
  unfold Sof
  split
  · rw [bracket0_eN_eN]; rfl
  · split
    · rw [bracket0_neg_right, bracket0_eN_eN]
      show -(bracket0Basis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n)
          (Sum.inr (Sum.inl ⟨(b, a), by assumption⟩))) = bracketSS i j a b
      rw [show (bracket0Basis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n)
          (Sum.inr (Sum.inl ⟨(b, a), by assumption⟩)) : OspMod F n) = bracketSS i j b a from rfl,
        bracketSS_swap34, neg_neg]
    · rename_i hab hba
      have : a = b := F.key_injective (le_antisymm (not_lt.mp hba) (not_lt.mp hab))
      subst this
      rw [bracket0_zero_right, bracketSS_diag]

/-- `hTilde_eN` and `hTildeBasis_Fof` chained, stated directly against the
raw `Sum.inr (Sum.inr (u, i))` shape rather than the `Fof u i` notation —
needed because once `Fof` has been unfolded by `simp` (as it must be, for
`bracket0Basis`'s own equations to fire), `hTildeBasis_Fof`'s `Fof`-headed
LHS can no longer match syntactically. -/
theorem hTilde_eN_raw {F : FermionIndex} {n : ℕ} (u : I n) (i : F.K) :
    hTilde (eN (Sum.inr (Sum.inr (u, i)) : OspBasis F n)) =
      (1 / 2 : ℚ) • ∑ j : F.K, beta F n u j • Sof (F.dual j) i := by
  rw [show (Sum.inr (Sum.inr (u, i)) : OspBasis F n) = Fof u i from rfl, hTilde_eN,
    hTildeBasis_Fof]

/-! ## `SF` sector — direct computation -/

theorem delta_hTilde_SF {F : FermionIndex} {n : ℕ} (i j : F.K) (hij : F.key i < F.key j)
  (w : I n) (p : F.K) :
    deltaBasis hTilde (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) (Fof w p)
      = GammaSF i j w p := by
  unfold deltaBasis
  have hterm1 : bracket0 (hTilde (eN (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n)))
      (eN (Fof w p)) = 0 := by
    rw [hTilde_eN]; simp only [hTildeBasis]; exact bracket0_zero_left _
  rw [hterm1, zero_add]
  simp only [show parity (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) = 0 from rfl,
    gsign_01, one_smul,
    hTilde_eN_raw, bracket0_smul_right_rat,
    bracket0_sum_right, bracket0_smul_right, bracket0_S_Sof, bracketSS,
    bracket0_eN_eN, bracket0Basis, bracketSF, Fof, sub_eq_add_neg, hTilde_add, hTilde_neg,
    hTilde_smul_rat, GammaSF]
  simp only [smul_add, smul_neg, Finset.sum_add_distrib]
  rw [show (∑ x : F.K, beta F n w x • F.g j (F.dual x) • Sof i p : OspMod F n)
      = beta F n w j • Sof i p from by
        rw [Finset.sum_eq_single j]
        · rw [show F.g j (F.dual j) = 1 from by rw [g_eq_dual]; simp [F.dual_dual], one_smul]
        · intro b _ hb
          rw [show F.g j (F.dual b) = 0 from by rw [g_eq_dual, F.dual_dual]; simp [hb.symm]]
          simp
        · intro h; exact absurd (Finset.mem_univ _) h,
      show (∑ x : F.K, -(beta F n w x • F.g i (F.dual x) • Sof j p) : OspMod F n)
      = -(beta F n w i • Sof j p) from by
        rw [Finset.sum_eq_single i]
        · rw [show F.g i (F.dual i) = 1 from by rw [g_eq_dual]; simp [F.dual_dual], one_smul]
        · intro b _ hb
          rw [show F.g i (F.dual b) = 0 from by rw [g_eq_dual, F.dual_dual]; simp [hb.symm]]
          simp
        · intro h; exact absurd (Finset.mem_univ _) h,
      show (∑ x : F.K, -(beta F n w x • F.g j p • Sof i (F.dual x)) : OspMod F n)
      = F.g j p • ∑ x : F.K, beta F n w x • Sof (F.dual x) i from by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [Sof_antisymm i (F.dual x), smul_neg, smul_neg, neg_neg]
        exact smul_comm (beta F n w x) (F.g j p) (Sof (F.dual x) i),
      show (∑ x : F.K, beta F n w x • F.g i p • Sof j (F.dual x) : OspMod F n)
      = -(F.g i p • ∑ x : F.K, beta F n w x • Sof (F.dual x) j) from by
        rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro x _
        rw [Sof_antisymm j (F.dual x), smul_neg, smul_neg]
        exact congrArg Neg.neg (smul_comm (beta F n w x) (F.g i p) (Sof (F.dual x) j))]
  set Ti := (∑ x : F.K, beta F n w x • Sof (F.dual x) i : OspMod F n) with hTi
  set Tj := (∑ x : F.K, beta F n w x • Sof (F.dual x) j : OspMod F n) with hTj
  set A := (beta F n w j • Sof i p : OspMod F n) with hA
  set B := (beta F n w i • Sof j p : OspMod F n) with hB
  clear_value Ti Tj A B
  simp only [smul_neg, smul_smul]
  rw [show (1 / 2 : ℚ) * F.g j p = F.g j p * (1 / 2) from mul_comm _ _,
    show (1 / 2 : ℚ) * F.g i p = F.g i p * (1 / 2) from mul_comm _ _]
  abel

/-- **FS**, derived from **SF** by the reversal shortcut: `p(S) = 0`,
`p(F) = 1`, `gsign 0 1 = 1`, so sign `-1`. -/
theorem delta_hTilde_FS {F : FermionIndex} {n : ℕ} (i j : F.K) (hij : F.key i < F.key j)
  (w : I n) (p : F.K) :
    deltaBasis hTilde (Fof w p : OspBasis F n) (Sum.inr (Sum.inl ⟨(i, j), hij⟩))
      = -GammaSF i j w p := by
  rw [deltaBasis_hTilde_swap (Sum.inr (Sum.inl ⟨(i, j), hij⟩)) (Fof w p), delta_hTilde_SF]
  simp [parity, Fof, gsign]

/-- `bracketSF` is antisymmetric in its first two arguments, the same pure
algebraic fact as `bracketSS_swap34`. -/
theorem bracketSF_swap12 {F : FermionIndex} {n : ℕ} (a b : F.K) (w : I n) (q : F.K) :
    (bracketSF a b w q : OspMod F n) = -bracketSF b a w q := by
  unfold bracketSF
  abel

/-- `bracketSF` vanishes when its first two arguments coincide. -/
theorem bracketSF_diag {F : FermionIndex} {n : ℕ} (a : F.K) (w : I n) (q : F.K) :
    (bracketSF a a w q : OspMod F n) = 0 := by
  unfold bracketSF
  abel

/-- `bracket0` against a basis point of `F`-kind matched on the *left*
against an arbitrary (not necessarily sorted) `Sof a b` on the right,
reduces to `bracketSF a b v q` — the mirror of `bracket0_S_Sof`, needed for
`hTildeBasis_Fof`'s sum against `eN (Fof v q)`. -/
theorem bracket0_Sof_Fof {F : FermionIndex} {n : ℕ} (a b : F.K) (v : I n) (q : F.K) :
    bracket0 (Sof a b : OspMod F n) (eN (Fof v q)) = bracketSF a b v q := by
  unfold Sof
  split
  · rw [bracket0_eN_eN]; rfl
  · split
    · rw [bracket0_neg_left, bracket0_eN_eN]
      rw [show (bracket0Basis (Sum.inr (Sum.inl ⟨(b, a), by assumption⟩) : OspBasis F n)
          (Fof v q) : OspMod F n) = bracketSF b a v q from rfl,
        bracketSF_swap12, neg_neg]
    · rename_i hab hba
      have : a = b := F.key_injective (le_antisymm (not_lt.mp hba) (not_lt.mp hab))
      subst this
      rw [bracket0_zero_left, bracketSF_diag]

/-- `bracket0` against a basis point of `F`-kind matched on the *right*
against an arbitrary `Sof a b` on the left — the `bracket0Basis` `FS`
branch's own extra minus sign carries through unconditionally too. -/
theorem bracket0_Fof_Sof {F : FermionIndex} {n : ℕ} (u : I n) (p : F.K) (a b : F.K) :
    bracket0 (eN (Fof u p) : OspMod F n) (Sof a b) = -bracketSF a b u p := by
  unfold Sof
  split
  · rw [bracket0_eN_eN]; rfl
  · split
    · rw [bracket0_neg_right, bracket0_eN_eN]
      rw [show (bracket0Basis (Fof u p : OspBasis F n)
          (Sum.inr (Sum.inl ⟨(b, a), by assumption⟩)) : OspMod F n) = -bracketSF b a u p from rfl,
        bracketSF_swap12, neg_neg]
    · rename_i hab hba
      have : a = b := F.key_injective (le_antisymm (not_lt.mp hba) (not_lt.mp hab))
      subst this
      rw [bracket0_zero_right, bracketSF_diag, neg_zero]

/-! ## `FF` sector — direct computation -/

theorem delta_hTilde_FF {F : FermionIndex} {n : ℕ} (u : I n) (p : F.K) (v : I n) (q : F.K) :
    deltaBasis hTilde (Fof u p : OspBasis F n) (Fof v q) = GammaFF u p v q := by
  unfold deltaBasis
  have hterm3 : hTilde (bracket0 (eN (Fof u p) : OspMod F n) (eN (Fof v q)))
      = (1 / 2 * F.g p q : ℚ) • ∑ l : F.K,
          (beta F n u (F.dual l) • eN (Fof v l) + beta F n v (F.dual l) • eN (Fof u l)) := by
    rw [bracket0_eN_eN]
    change hTilde (bracketFF u p v q) = _
    unfold bracketFF
    rw [hTilde_add, hTilde_smul_rat, hTilde_smul_rat, hTilde_Sof, smul_zero, zero_add,
      hTilde_eN, hTildeBasis_Lof]
  have hterm1 : bracket0 (hTilde (eN (Fof u p) : OspMod F n)) (eN (Fof v q))
      = (1 / 2 : ℚ) • ∑ l : F.K, beta F n u l • bracketSF (F.dual l) p v q := by
    rw [hTilde_eN, hTildeBasis_Fof, bracket0_smul_left_rat]
    congr 1
    rw [bracket0_sum_left]
    apply Finset.sum_congr rfl
    intro l _
    rw [bracket0_smul_left, bracket0_Sof_Fof]
  have hterm2 : bracket0 (eN (Fof u p) : OspMod F n) (hTilde (eN (Fof v q)))
      = (1 / 2 : ℚ) • ∑ l : F.K, beta F n v l • (-bracketSF (F.dual l) q u p) := by
    rw [hTilde_eN, hTildeBasis_Fof, bracket0_smul_right_rat]
    refine congrArg (fun z => (1 / 2 : ℚ) • z) ?_
    rw [bracket0_sum_right]
    apply Finset.sum_congr rfl
    intro l _
    rw [bracket0_smul_right, bracket0_Fof_Sof]
  rw [hterm3, hterm1, hterm2, show (parity (Fof u p) : ZMod 2) = 1 from rfl, gsign_11]
  simp only [bracketSF, smul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, one_smul, neg_smul, neg_sub]
  have hreindex_v : (∑ x : F.K, beta F n u x • eN (Fof v (F.dual x)) : OspMod F n)
      = ∑ x : F.K, beta F n u (F.dual x) • eN (Fof v x) := by
    have h := sum_dual (M := OspMod F n) (fun x => beta F n u (F.dual x) • eN (Fof v x))
    simp only [F.dual_dual] at h
    exact h
  have hreindex_u : (∑ x : F.K, beta F n v x • eN (Fof u (F.dual x)) : OspMod F n)
      = ∑ x : F.K, beta F n v (F.dual x) • eN (Fof u x) := by
    have h := sum_dual (M := OspMod F n) (fun x => beta F n v (F.dual x) • eN (Fof u x))
    simp only [F.dual_dual] at h
    exact h
  rw [show (∑ x : F.K, beta F n u x • F.g p q • eN (Fof v (F.dual x)) : OspMod F n)
      = F.g p q • ∑ x : F.K, beta F n u (F.dual x) • eN (Fof v x) from by
        rw [show (∑ x : F.K, beta F n u x • F.g p q • eN (Fof v (F.dual x)) : OspMod F n)
            = ∑ x : F.K, F.g p q • (beta F n u x • eN (Fof v (F.dual x))) from
              Finset.sum_congr rfl (fun x _ => smul_comm _ _ _),
          ← Finset.smul_sum, hreindex_v],
      show (∑ x : F.K, beta F n v x • F.g q p • eN (Fof u (F.dual x)) : OspMod F n)
      = F.g p q • ∑ x : F.K, beta F n v (F.dual x) • eN (Fof u x) from by
        rw [F.g_symm,
          show (∑ x : F.K, beta F n v x • F.g p q • eN (Fof u (F.dual x)) : OspMod F n)
            = ∑ x : F.K, F.g p q • (beta F n v x • eN (Fof u (F.dual x))) from
              Finset.sum_congr rfl (fun x _ => smul_comm _ _ _),
          ← Finset.smul_sum, hreindex_u],
      show (∑ x : F.K, beta F n u x • F.g (F.dual x) q • eN (Fof v p) : OspMod F n)
      = beta F n u q • eN (Fof v p) from by
        rw [Finset.sum_eq_single q]
        · rw [show F.g (F.dual q) q = 1 from by rw [g_eq_dual]; simp, one_smul]
        · intro b _ hb
          rw [show F.g (F.dual b) q = 0 from by
                rw [g_eq_dual]
                have : F.dual b ≠ F.dual q := fun he => hb (by
                  rw [← F.dual_dual b, he, F.dual_dual])
                simp [this]]
          simp
        · intro h; exact absurd (Finset.mem_univ _) h,
      show (∑ x : F.K, beta F n v x • F.g (F.dual x) p • eN (Fof u q) : OspMod F n)
      = beta F n v p • eN (Fof u q) from by
        rw [Finset.sum_eq_single p]
        · rw [show F.g (F.dual p) p = 1 from by rw [g_eq_dual]; simp, one_smul]
        · intro b _ hb
          rw [show F.g (F.dual b) p = 0 from by
                rw [g_eq_dual]
                have : F.dual b ≠ F.dual p := fun he => hb (by
                  rw [← F.dual_dual b, he, F.dual_dual])
                simp [this]]
          simp
        · intro h; exact absurd (Finset.mem_univ _) h]
  unfold GammaFF
  set T1 := (∑ x : F.K, beta F n u (F.dual x) • eN (Fof v x) : OspMod F n)
  set T2 := (∑ x : F.K, beta F n v (F.dual x) • eN (Fof u x) : OspMod F n)
  set C1 := (beta F n u q • eN (Fof v p) : OspMod F n)
  set C2 := (beta F n v p • eN (Fof u q) : OspMod F n)
  clear_value T1 T2 C1 C2
  simp only [smul_add, smul_smul, neg_smul]
  rw [show (1 / 2 : ℚ) * F.g p q = F.g p q * (1 / 2) from mul_comm _ _]
  abel

/-- **`Γ_β = δh̃`**, basis level: on every ordered basis pair, assembled
from the nine sector theorems above (`LL`/`SS` free, `LF`/`LS`/`SF` direct,
`FL`/`SL`/`FS` by the reversal shortcut, `FF` direct). -/
theorem Gamma_eq_delta_hTilde_basis {F : FermionIndex} {n : ℕ} (X Y : OspBasis F n) :
    GammaBasis X Y = deltaBasis hTilde X Y := by
  match X, Y with
  | .inl ⟨(u, v), hp⟩, .inl ⟨(w, z), hq⟩ => exact (delta_hTilde_LL u v w z hp hq).symm
  | .inl ⟨(u, v), hp⟩, .inr (.inl ⟨(i, j), hij⟩) => exact (delta_hTilde_LS u v i j hp hij).symm
  | .inl ⟨(u, v), hp⟩, .inr (.inr (w, k)) => exact (delta_hTilde_LF u v w k hp).symm
  | .inr (.inl ⟨(i, j), hij⟩), .inl ⟨(u, v), hp⟩ => exact (delta_hTilde_SL u v i j hp hij).symm
  | .inr (.inl ⟨(i, j), hij⟩), .inr (.inl ⟨(k, l), hkl⟩) =>
    exact (delta_hTilde_SS i j k l hij hkl).symm
  | .inr (.inl ⟨(i, j), hij⟩), .inr (.inr (w, k)) => exact (delta_hTilde_SF i j hij w k).symm
  | .inr (.inr (w, k)), .inl ⟨(u, v), hp⟩ => exact (delta_hTilde_FL u v w k hp).symm
  | .inr (.inr (w, k)), .inr (.inl ⟨(i, j), hij⟩) => exact (delta_hTilde_FS i j hij w k).symm
  | .inr (.inr (u, p)), .inr (.inr (v, q)) => exact (delta_hTilde_FF u p v q).symm

/-- **`Γ_β = δh̃`**, the bilinear extension to arbitrary elements of `OspMod F n`:
`Gamma`/`delta` are both literally the same double sum shape against
`GammaBasis`/`deltaBasis hTilde`, which now agree termwise by
`Gamma_eq_delta_hTilde_basis`. -/
theorem Gamma_eq_delta_hTilde {F : FermionIndex} {n : ℕ} (x y : OspMod F n) :
    Gamma x y = delta hTilde x y := by
  unfold Gamma delta
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Gamma_eq_delta_hTilde_basis]

end OspN
end OspOddDeformations
