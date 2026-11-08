import OspOddDeformations.OspN.Multi.CompFormulas

/-!
# Reduction of `intertwining_multi` to the core identity

The `(x, y)`-free identity `CoreId Θ` (all basis pairs, coefficient by coefficient) implies the
intertwining for all `x y`, given that `u X W = grComp (UBasis0 Θ X) W` has parity
`parity X + parity W`.
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

/-- The `W`-coefficient of `U X`, as an element of `GR`. -/
noncomputable def uMat (Θ : I n → I n → GR F n r) (X W : OspBasis F n) : GR F n r :=
  grComp (UBasis0 Θ X) W

theorem sigPow_smul (π : ZMod 2) (c : PmnR F n r) (a : GR F n r) :
    sigPow π (c • a) = c • sigPow π a := by
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hz π with rfl | rfl
  · simp [sigPow_zero]
  · have h1 : (1 : ZMod 2) ≠ 0 := by decide
    simp [sigPow, h1, sig_smul]

theorem sum_comm4' {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid M] (f : α → β → γ → δ → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem core_term (π ρ : ZMod 2) (x y u u' : GR F n r) (hu : HasParity (π + ρ) u) :
    gmul (gmul x u) (sigPow ρ (gmul y u')) =
      gmul (gmul x (sigPow π y)) (gmul u (sigPow ρ u')) := by
  rw [sigPow_gmul, gmul_assoc, ← gmul_assoc u, gmul_comm_hom hu, sigPow_add]
  have : π + ρ + ρ = π := by
    have hz : ∀ z w : ZMod 2, z + w + w = z := by decide
    exact hz π ρ
  rw [this, gmul_assoc, gmul_assoc]

/-- The left side of the core identity: `[U X, U Y]_0`, at the `V`-coefficient. -/
noncomputable def coreL (Θ : I n → I n → GR F n r) (X Y V : OspBasis F n) : GR F n r :=
  ∑ W : OspBasis F n, ∑ W' : OspBasis F n, emb0 (r := r) (bracket0Basis W W' V) •
    gmul (uMat Θ X W) (sigPow (parity W) (uMat Θ Y W'))

/-- The right side of the core identity: `U [X,Y]_β`, at the `V`-coefficient. -/
noncomputable def coreR (Θ : I n → I n → GR F n r) (X Y V : OspBasis F n) : GR F n r :=
  ∑ V' : OspBasis F n, (emb0 (r := r) (bracket0Basis X Y V') • uMat Θ V' V +
    ∑ s : Fin r, embS s (GammaBasis X Y V') • gmul (gmono {s} 1) (uMat Θ V' V))

/-- The core identity: the intertwining for basis symbols with no `κ`-factors. -/
def CoreId (Θ : I n → I n → GR F n r) : Prop := ∀ X Y V, coreL Θ X Y V = coreR Θ X Y V

theorem stepL (Θ : I n → I n → GR F n r)
    (hpar : ∀ X W, HasParity (parity X + parity W) (uMat Θ X W)) (x y : RModM F n r)
    (V : OspBasis F n) :
    grComp (bracket0M (UM Θ x) (UM Θ y)) V = ∑ Z : OspBasis F n, ∑ Z' : OspBasis F n,
      gmul (gmul (grComp x Z) (sigPow (parity Z) (grComp y Z'))) (coreL Θ Z Z' V) := by
  rw [grComp_bracket0M]
  simp only [grComp_UM, coreL]
  have key : ∀ W W' : OspBasis F n,
      gmul (∑ Z, gmul (grComp x Z) (grComp (UBasis0 Θ Z) W))
        (sigPow (parity W) (∑ Z', gmul (grComp y Z') (grComp (UBasis0 Θ Z') W'))) =
      ∑ Z, ∑ Z', gmul (gmul (grComp x Z) (sigPow (parity Z) (grComp y Z')))
        (gmul (uMat Θ Z W) (sigPow (parity W) (uMat Θ Z' W'))) := by
    intro W W'
    rw [sigPow_sum, gmul_sum_left]
    refine Finset.sum_congr rfl fun Z _ => ?_
    rw [gmul_sum_right]
    refine Finset.sum_congr rfl fun Z' _ => ?_
    exact core_term (parity Z) (parity W) _ _ _ _ (hpar Z W)
  simp only [key, Finset.smul_sum]
  rw [sum_comm4']
  refine Finset.sum_congr rfl fun Z _ => Finset.sum_congr rfl fun Z' _ => ?_
  rw [gmul_sum_right]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [gmul_sum_right]
  refine Finset.sum_congr rfl fun W' _ => ?_
  rw [gmul_smul_right]

theorem stepR (Θ : I n → I n → GR F n r) (x y : RModM F n r) (V : OspBasis F n) :
    grComp (UM Θ (bracketBetaM x y)) V = ∑ Z : OspBasis F n, ∑ Z' : OspBasis F n,
      gmul (gmul (grComp x Z) (sigPow (parity Z) (grComp y Z'))) (coreR Θ Z Z' V) := by
  rw [grComp_UM]
  simp only [grComp_bracketBetaM, grComp_bracket0M, gmul_add_left, gmul_sum_left, gmul_smul_left,
    Finset.sum_add_distrib]
  simp only [coreR, gmul_sum_right, gmul_add_right, gmul_smul_right, Finset.sum_add_distrib,
    gmul_assoc]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun Z _ => Finset.sum_comm
  · rw [sum_comm4']
    exact Finset.sum_congr rfl fun Z _ => Finset.sum_congr rfl fun Z' _ =>
      Finset.sum_congr rfl fun V' _ => Finset.sum_congr rfl fun s _ => rfl

/-- **Reduction.** The core identity (basis symbols, no `κ`-factors) implies the intertwining. -/
theorem intertwining_of_core (Θ : I n → I n → GR F n r)
    (hpar : ∀ X W, HasParity (parity X + parity W) (uMat Θ X W)) (hcore : CoreId Θ)
    (x y : RModM F n r) :
    bracket0M (UM Θ x) (UM Θ y) = UM Θ (bracketBetaM x y) := by
  funext ⟨V, T⟩
  have h : grComp (bracket0M (UM Θ x) (UM Θ y)) V = grComp (UM Θ (bracketBetaM x y)) V := by
    rw [stepL Θ hpar, stepR]
    refine Finset.sum_congr rfl fun Z _ => Finset.sum_congr rfl fun Z' _ => ?_
    rw [hcore Z Z' V]
  exact congrFun h T

end Multi
end OspN
end OspOddDeformations
