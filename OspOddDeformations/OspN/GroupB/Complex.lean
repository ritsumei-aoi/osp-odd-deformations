import OspOddDeformations.OspN.Normalization
import OspOddDeformations.General.StructureConstants
import Mathlib.Basic.Complex.Basic

/-!
# Cor 4.11 (complex parameters)

For any values `b : I × K_N → ℂ` of the `β_{u,i}`, the specialized bracket on `(ℂ ⊕ κℂ) ⊗ 𝔤`
(`bracketRBetaC b`, the bracket of `[·,·]_β` with `β = b`) is carried to the undeformed one
(`bracketRC b`) by `id + κ f_β` at `β = b` (`TBetaC b`), which is bijective (`TBetaC_bijective`).
The proof specializes the identity of Cor 4.8 (`intertwining_fBeta`), proved over `ℚ[β]`, through
`MvPolynomial.eval₂Hom`, by `General.intertwine_map`.
-/

namespace OspOddDeformations
namespace OspN

open General

variable {F : FermionIndex} {n : ℕ}

/-- `β ↦ b`, `ℚ[β] → ℂ`. -/
noncomputable def specC (b : Bmn.I n × F.K → ℂ) : Pmn F n →+* ℂ :=
  MvPolynomial.eval₂Hom (Rat.castHom ℂ) b

variable (b : Bmn.I n × F.K → ℂ)

/-- The undeformed bracket on `(ℂ ⊕ κℂ) ⊗ 𝔤`. -/
noncomputable def bracketRC (x y : RBasis F n → ℂ) : RBasis F n → ℂ :=
  bilOf (fun p q => specC b ∘ bracketRBasis p q) x y

/-- The bracket `[·,·]_β` at `β = b`. -/
noncomputable def bracketRBetaC (x y : RBasis F n → ℂ) : RBasis F n → ℂ :=
  bilOf (fun p q => specC b ∘ bracketRBetaBasis p q) x y

/-- `id + κ f_β` at `β = b`. -/
noncomputable def TBetaC (x : RBasis F n → ℂ) : RBasis F n → ℂ :=
  linOf (fun p => specC b ∘ TBetaF (eR p)) x

/-- Its inverse `id − κ f_β` at `β = b`. -/
noncomputable def TBetaInvC (x : RBasis F n → ℂ) : RBasis F n → ℂ :=
  linOf (fun p => specC b ∘ TBetaFInv (eR p)) x

theorem TBetaF_eq_linOf (r : RMod F n) : TBetaF r = linOf (fun p => TBetaF (eR p)) r := by
  conv_lhs => rw [eR_decompose r]
  rw [TBetaF_sum']
  rfl

theorem TBetaFInv_add (r1 r2 : RMod F n) :
    TBetaFInv (r1 + r2) = TBetaFInv r1 + TBetaFInv r2 := by
  rw [TBetaFInv_eq, TBetaFInv_eq, TBetaFInv_eq, falsePart_add, fBeta_add, kappaEmbed_add]
  abel

theorem TBetaFInv_smul (c : Pmn F n) (r : RMod F n) : TBetaFInv (c • r) = c • TBetaFInv r := by
  rw [TBetaFInv_eq, TBetaFInv_eq, falsePart_smul, fBeta_smul, kappaEmbed_smul, smul_sub]

theorem TBetaFInv_zero : TBetaFInv (0 : RMod F n) = 0 := by
  simpa using TBetaFInv_smul (F := F) (n := n) 0 0

theorem TBetaFInv_eq_linOf (r : RMod F n) :
    TBetaFInv r = linOf (fun p => TBetaFInv (eR p)) r := by
  conv_lhs => rw [eR_decompose r]
  unfold linOf
  induction (Finset.univ : Finset (RBasis F n)) using Finset.induction with
  | empty => simp [TBetaFInv_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, TBetaFInv_add, TBetaFInv_smul, ih, Finset.sum_insert ha]

theorem bracketR_eq_bilOf (x y : RMod F n) : bracketR x y = bilOf bracketRBasis x y := rfl

theorem bracketRBeta_eq_bilOf (x y : RMod F n) : bracketRBeta x y = bilOf bracketRBetaBasis x y :=
  rfl

/-- **Cor 4.11 (complex parameters)**: for every `b`, `id + κ f_β` (at `β = b`) carries the
specialized bracket to the undeformed one. -/
theorem complex_parameters (x y : RBasis F n → ℂ) :
    bracketRC b (TBetaC b x) (TBetaC b y) = TBetaC b (bracketRBetaC b x y) := by
  apply intertwine_map
  intro p q
  rw [← bracketR_eq_bilOf, intertwining_fBeta, bracketRBeta_eR_eR, TBetaF_eq_linOf]

theorem TBetaInvC_TBetaC (x : RBasis F n → ℂ) : TBetaInvC b (TBetaC b x) = x := by
  unfold TBetaInvC TBetaC
  rw [linOf_linOf]
  conv_rhs => rw [← linOf_eB_cols x]
  congr 1
  funext p
  rw [← map_linOf, ← TBetaFInv_eq_linOf, TBetaFInv_TBetaF]
  funext k
  by_cases h : k = p <;> simp [eR, eB, h]

theorem TBetaC_TBetaInvC (x : RBasis F n → ℂ) : TBetaC b (TBetaInvC b x) = x := by
  unfold TBetaInvC TBetaC
  rw [linOf_linOf]
  conv_rhs => rw [← linOf_eB_cols x]
  congr 1
  funext p
  rw [← map_linOf, ← TBetaF_eq_linOf, TBetaF_TBetaFInv]
  funext k
  by_cases h : k = p <;> simp [eR, eB, h]

/-- `id + κ f_β` at `β = b` is bijective. -/
theorem TBetaC_bijective : Function.Bijective (TBetaC (F := F) b) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨TBetaInvC b, TBetaInvC_TBetaC b, TBetaC_TBetaInvC b⟩

end OspN
end OspOddDeformations
