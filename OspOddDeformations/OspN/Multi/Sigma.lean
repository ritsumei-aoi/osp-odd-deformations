import OspOddDeformations.OspN.Multi.Theta

/-!
# The grading automorphism `sig` of `GR`

`sig a T = (-1)^{|T|} a T`, an algebra automorphism of `(GR, gmul)`; `sigPow π` is `sig^π`.
Homogeneous elements commute up to `sig`: `gmul a b = gmul (sigPow π b) a` if `a` has parity `π`.
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

/-- `κ_T ↦ (-1)^{|T|} κ_T`. -/
noncomputable def sig (a : GR F n r) : GR F n r := fun T => ((-1 : ℚ) ^ T.card) • a T

/-- `sig ^ π`. -/
noncomputable def sigPow (π : ZMod 2) (a : GR F n r) : GR F n r := if π = 0 then a else sig a

/-- `a` is supported on sets of cardinality `≡ π (mod 2)`. -/
def HasParity (π : ZMod 2) (a : GR F n r) : Prop := ∀ T, (T.card : ZMod 2) ≠ π → a T = 0

theorem sig_apply (a : GR F n r) (T : Finset (Fin r)) : sig a T = ((-1 : ℚ) ^ T.card) • a T := rfl

theorem sig_add (a b : GR F n r) : sig (a + b) = sig a + sig b := by
  funext T; simp [sig, smul_add]

theorem sig_zero : sig (0 : GR F n r) = 0 := by funext T; simp [sig]

theorem sig_neg (a : GR F n r) : sig (-a) = - sig a := by funext T; simp [sig]

theorem sig_rsmul (q : ℚ) (a : GR F n r) : sig (q • a) = q • sig a := by
  funext T
  simp only [sig, Pi.smul_apply]
  exact smul_comm _ _ _

theorem sig_smul (c : PmnR F n r) (a : GR F n r) : sig (c • a) = c • sig a := by
  funext T
  simp only [sig, Pi.smul_apply, smul_eq_mul]
  rw [Algebra.smul_def, Algebra.smul_def]
  simp [mul_left_comm]

theorem sig_sum {ι : Type*} (s : Finset ι) (f : ι → GR F n r) :
    sig (∑ i ∈ s, f i) = ∑ i ∈ s, sig (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [sig_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, sig_add, ih]

theorem sig_sig (a : GR F n r) : sig (sig a) = a := by
  funext T; simp [sig, smul_smul, ← pow_add, ← two_mul, pow_mul]

theorem sig_gone : sig (gone : GR F n r) = gone := by
  funext T
  by_cases h : T = ∅ <;> simp [sig, gone, h]

theorem sig_gmul (a b : GR F n r) : sig (gmul a b) = gmul (sig a) (sig b) := by
  funext T
  simp only [sig, gmul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
  by_cases hU : A ∪ B = T
  · simp only [hU, ite_true]
    by_cases hd : Disjoint A B
    · rw [← hU, Finset.card_union_of_disjoint hd]
      simp [smul_smul, pow_add, mul_comm, mul_assoc]
    · simp [gs_eq_zero_of_not_disjoint hd]
  · simp [hU]

theorem sigPow_apply (π : ZMod 2) (a : GR F n r) (T : Finset (Fin r)) :
    sigPow π a T = ((-1 : ℚ) ^ (π.val * T.card)) • a T := by
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hz π with rfl | rfl
  · simp [sigPow]
  · have : (1 : ZMod 2).val = 1 := rfl
    have h1 : (1 : ZMod 2) ≠ 0 := by decide
    simp [sigPow, h1, this, sig]

theorem sigPow_zero (a : GR F n r) : sigPow 0 a = a := by simp [sigPow]

theorem sigPow_gmul (π : ZMod 2) (a b : GR F n r) :
    sigPow π (gmul a b) = gmul (sigPow π a) (sigPow π b) := by
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hz π with rfl | rfl
  · simp [sigPow_zero]
  · have h1 : (1 : ZMod 2) ≠ 0 := by decide
    simp [sigPow, h1, sig_gmul]

/-- Homogeneous elements commute up to `sig`. -/
theorem gmul_comm_hom {π : ZMod 2} {a : GR F n r} (ha : HasParity π a) (b : GR F n r) :
    gmul a b = gmul (sigPow π b) a := by
  funext T
  simp only [gmul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun B _ => Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.union_comm B A]
  by_cases hA : a A = 0
  · simp [hA]
  · have hc : (A.card : ZMod 2) = π := by
      by_contra hc; exact hA (ha A hc)
    split_ifs with hU
    · have hA2 : A.card % 2 = π.val := by rw [← hc, ZMod.val_natCast]
      have hm : (A.card * B.card) % 2 = (π.val * B.card) % 2 := by
        have hmod : A.card ≡ π.val [MOD 2] := by
          unfold Nat.ModEq; rw [hA2]; exact (Nat.mod_eq_of_lt (ZMod.val_lt π)).symm
        exact Nat.ModEq.mul_right _ hmod
      have hpow : (-1 : ℚ) ^ (A.card * B.card) = (-1) ^ (π.val * B.card) := by
        rw [neg_one_pow_eq_pow_mod_two, hm, ← neg_one_pow_eq_pow_mod_two]
      rw [gs_comm A B, sigPow_apply, hpow, smul_mul_assoc, mul_comm (a A) (b B), smul_smul]
      simp only [mul_comm (gs B A)]
    · rfl

theorem sigPow_add (π ρ : ZMod 2) (a : GR F n r) : sigPow π (sigPow ρ a) = sigPow (π + ρ) a := by
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have h1 : (1 : ZMod 2) ≠ 0 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases hz π with rfl | rfl <;> rcases hz ρ with rfl | rfl
  · simp [sigPow_zero]
  · simp [sigPow_zero]
  · simp [sigPow_zero]
  · simp [sigPow, h1, h11, sig_sig]

theorem sigPow_sigPow_self (π : ZMod 2) (a : GR F n r) : sigPow π (sigPow π a) = a := by
  rw [sigPow_add]
  have : π + π = 0 := by
    have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases hz π with rfl | rfl <;> decide
  rw [this, sigPow_zero]

theorem sigPow_add_apply (π : ZMod 2) (a b : GR F n r) :
    sigPow π (a + b) = sigPow π a + sigPow π b := by
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hz π with rfl | rfl
  · simp [sigPow_zero]
  · have h1 : (1 : ZMod 2) ≠ 0 := by decide
    simp [sigPow, h1, sig_add]

theorem sigPow_sum (π : ZMod 2) {ι : Type*} (s : Finset ι) (f : ι → GR F n r) :
    sigPow π (∑ i ∈ s, f i) = ∑ i ∈ s, sigPow π (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [sigPow, sig_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, sigPow_add_apply, ih]

end Multi
end OspN
end OspOddDeformations
