import OspOddDeformations.OspN.Multi.Sigma
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module
import Mathlib.Tactic.Abel

/-!
# `GR` as a ring

`GRing F n r` is a type synonym for `GR F n r` carrying the `ℚ`-algebra structure with product
`gmul` and unit `gone` (`Multi/Grassmann.lean`). The definitions stay on `GR`; only proofs use
the synonym.
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

noncomputable section

variable {F : FermionIndex} {n r : ℕ}

/-- `GR F n r` with its multiplication `gmul`, as a ring. -/
def GRing (F : FermionIndex) (n r : ℕ) : Type := GR F n r

namespace GRing

/-- The identity map `GR → GRing`. -/
def ofGR (a : GR F n r) : GRing F n r := a
/-- The identity map `GRing → GR`. -/
def toGR (a : GRing F n r) : GR F n r := a

instance : AddCommGroup (GRing F n r) :=
  inferInstanceAs (AddCommGroup (Finset (Fin r) → PmnR F n r))

instance : Module ℚ (GRing F n r) :=
  inferInstanceAs (Module ℚ (Finset (Fin r) → PmnR F n r))

instance : Module (PmnR F n r) (GRing F n r) :=
  inferInstanceAs (Module (PmnR F n r) (Finset (Fin r) → PmnR F n r))

instance : Mul (GRing F n r) := ⟨fun a b => ofGR (gmul (toGR a) (toGR b))⟩
instance : One (GRing F n r) := ⟨ofGR gone⟩

theorem mul_def (a b : GRing F n r) : a * b = ofGR (gmul (toGR a) (toGR b)) := rfl
theorem one_def : (1 : GRing F n r) = ofGR gone := rfl

instance : NatCast (GRing F n r) := ⟨Nat.unaryCast⟩
instance : IntCast (GRing F n r) := ⟨Int.castDef⟩

instance : Ring (GRing F n r) :=
  { (inferInstance : AddCommGroup (GRing F n r)) with
    mul_assoc := fun a b c => gmul_assoc (toGR a) (toGR b) (toGR c)
    one_mul := fun a => gone_gmul (toGR a)
    mul_one := fun a => gmul_gone (toGR a)
    left_distrib := fun a b c => gmul_add_right (toGR a) (toGR b) (toGR c)
    right_distrib := fun a b c => gmul_add_left (toGR a) (toGR b) (toGR c)
    zero_mul := fun a => gmul_zero_left (toGR a)
    mul_zero := fun a => gmul_zero_right (toGR a)
    natCast_zero := rfl
    natCast_succ := fun _ => rfl
    intCast_ofNat := fun _ => rfl
    intCast_negSucc := fun _ => rfl }

instance : Algebra ℚ (GRing F n r) :=
  Algebra.ofModule (fun q a b => gmul_rsmul_left q (toGR a) (toGR b))
    (fun q a b => gmul_rsmul_right q (toGR a) (toGR b))

/-! ### Bridge lemmas -/

@[simp] theorem ofGR_gmul (a b : GR F n r) : ofGR (gmul a b) = ofGR a * ofGR b := rfl
@[simp] theorem ofGR_gone : (ofGR gone : GRing F n r) = 1 := rfl
@[simp] theorem toGR_mul (a b : GRing F n r) : toGR (a * b) = gmul (toGR a) (toGR b) := rfl
@[simp] theorem toGR_one : toGR (1 : GRing F n r) = gone := rfl
@[simp] theorem ofGR_add (a b : GR F n r) : (ofGR (a + b) : GRing F n r) = ofGR a + ofGR b := rfl
@[simp] theorem ofGR_sub (a b : GR F n r) : (ofGR (a - b) : GRing F n r) = ofGR a - ofGR b := rfl
@[simp] theorem ofGR_neg (a : GR F n r) : (ofGR (-a) : GRing F n r) = - ofGR a := rfl
@[simp] theorem ofGR_zero : (ofGR 0 : GRing F n r) = 0 := rfl
@[simp] theorem ofGR_rsmul (q : ℚ) (a : GR F n r) : (ofGR (q • a) : GRing F n r) = q • ofGR a :=
  rfl
@[simp] theorem ofGR_smul (c : PmnR F n r) (a : GR F n r) :
    (ofGR (c • a) : GRing F n r) = c • ofGR a := rfl
theorem ofGR_sum {ι : Type*} (s : Finset ι) (f : ι → GR F n r) :
    (ofGR (∑ i ∈ s, f i) : GRing F n r) = ∑ i ∈ s, ofGR (f i) := rfl
@[simp] theorem toGR_ofGR (a : GR F n r) : toGR (ofGR a : GRing F n r) = a := rfl
@[simp] theorem ofGR_toGR (a : GRing F n r) : ofGR (toGR a) = a := rfl

theorem ext_iff' (a b : GRing F n r) : a = b ↔ ∀ T, toGR a T = toGR b T :=
  ⟨fun h _ => h ▸ rfl, fun h => funext h⟩

/-- `PmnR`-scalars pass through the ring product. -/
theorem smul_mul_smul_left (c : PmnR F n r) (a b : GRing F n r) : (c • a) * b = c • (a * b) :=
  gmul_smul_left c (toGR a) (toGR b)

theorem mul_smul_smul_right (c : PmnR F n r) (a b : GRing F n r) : a * (c • b) = c • (a * b) :=
  gmul_smul_right c (toGR a) (toGR b)

/-- Even elements are central. -/
theorem mul_comm_of_even {a : GRing F n r} (ha : IsEvenGR (toGR a)) (b : GRing F n r) :
    a * b = b * a := gmul_comm_of_even ha (toGR b)

theorem sig_of_odd {b : GR F n r} (hb : HasParity 1 b) : sig b = - b := by
  funext T
  by_cases h : b T = 0
  · simp [sig, h]
  · have hc : (T.card : ZMod 2) = 1 := by
      by_contra hc; exact h (hb T hc)
    have : T.card % 2 = 1 := by
      have := (ZMod.natCast_eq_natCast_iff' T.card 1 2).mp (by simpa using hc)
      simpa using this
    simp [sig, Odd.neg_one_pow (Nat.odd_iff.mpr this)]

/-- Odd elements anticommute. -/
theorem mul_anticomm_of_odd {a b : GRing F n r} (ha : HasParity 1 (toGR a))
    (hb : HasParity 1 (toGR b)) : a * b = - (b * a) := by
  have h := gmul_comm_hom ha (toGR b)
  have h1 : sigPow 1 (toGR b) = - toGR b := by
    have : (1 : ZMod 2) ≠ 0 := by decide
    simp [sigPow, this, sig_of_odd hb]
  rw [h1] at h
  change gmul (toGR a) (toGR b) = - gmul (toGR b) (toGR a)
  rw [h, gmul_neg_left]

example (a b c d : GRing F n r) : (a + b) * (c - d) = a * c - a * d + b * c - b * d := by
  noncomm_ring

example (a b : GRing F n r) (q : ℚ) : q • (a * b) = (q • a) * b := by
  rw [smul_mul_assoc]

example (a b : GRing F n r) : a + b - a = b := by abel

end GRing

end

end Multi
end OspN
end OspOddDeformations
