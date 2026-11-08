import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring

/-!
# Bilinear and linear maps given by structure constants, under a change of coefficient ring

For a finite index type `B` and a commutative ring `R`, a family `c : B → B → (B → R)` defines
the bilinear map `bilOf c x y = Σ_{p,q} (x p * y q) • c p q` on `B → R`, and `t : B → (B → R)`
the linear map `linOf t x = Σ_p x p • t p`. A ring homomorphism `φ : R →+* S` carries both to
`B → S` with the constants `φ ∘ c`, `φ ∘ t`, and commutes with them (`map_bilOf`,
`map_linOf`). Hence an identity
between such maps on basis vectors over `R` gives the same identity over `S` for **all** arguments
(`intertwine_map`): this is how an identity proved over a polynomial ring is specialized to any
values of the variables, with arbitrary (not only specialized) arguments.

This file depends on mathlib only.
-/

namespace OspOddDeformations
namespace General

open Finset

variable {B : Type*} [Fintype B] {R S : Type*} [CommRing R] [CommRing S]

/-- The bilinear map with structure constants `c`. -/
def bilOf (c : B → B → B → R) (x y : B → R) : B → R := ∑ p, ∑ q, (x p * y q) • c p q

/-- The linear map with columns `t`. -/
def linOf (t : B → B → R) (x : B → R) : B → R := ∑ p, x p • t p

/-- The basis vector `e_p`. -/
def eB [DecidableEq B] (p : B) : B → R := fun q => if q = p then 1 else 0

theorem bilOf_eB [DecidableEq B] (c : B → B → B → R) (p q : B) :
    bilOf c (eB p) (eB q) = c p q := by
  simp [bilOf, eB, Finset.sum_ite_eq']

theorem linOf_eB [DecidableEq B] (t : B → B → R) (p : B) : linOf t (eB p) = t p := by
  simp [linOf, eB, ite_smul, Finset.sum_ite_eq']

/-- `bilOf` is bilinear: its value on combinations of the `u a`, `v b`. -/
theorem bilOf_linOf (c : B → B → B → R) (u v : B → B → R) (x y : B → R) :
    bilOf c (linOf u x) (linOf v y) = ∑ a, ∑ b, (x a * y b) • bilOf c (u a) (v b) := by
  funext k
  simp only [bilOf, linOf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  conv_lhs => enter [2, p, 2, q]; rw [Finset.sum_comm]
  conv_lhs => enter [2, p]; rw [Finset.sum_comm]
  conv_lhs => enter [2, p, 2, a]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

/-- `linOf` is linear: its value on `bilOf`. -/
theorem linOf_bilOf (t : B → B → R) (c : B → B → B → R) (x y : B → R) :
    linOf t (bilOf c x y) = ∑ a, ∑ b, (x a * y b) • linOf t (c a b) := by
  funext k
  simp only [bilOf, linOf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun p _ => ?_
  ring

theorem map_bilOf (φ : R →+* S) (c : B → B → B → R) (x y : B → R) :
    (φ ∘ bilOf c x y) = bilOf (fun p q => φ ∘ c p q) (φ ∘ x) (φ ∘ y) := by
  funext k
  simp [bilOf, Finset.sum_apply, map_sum, map_mul]

theorem map_linOf (φ : R →+* S) (t : B → B → R) (x : B → R) :
    (φ ∘ linOf t x) = linOf (fun p => φ ∘ t p) (φ ∘ x) := by
  funext k
  simp [linOf, Finset.sum_apply, map_sum, map_mul]

/-- An intertwining `bilOf c (T e_p) (T e_q) = T (bilOf c' e_p e_q)` over `R`, with `T = linOf t`,
gives `bilOf (φc) (T_φ x) (T_φ y) = T_φ (bilOf (φc') x y)` over `S` for all `x y : B → S`. -/
theorem intertwine_map (φ : R →+* S) (c c' : B → B → B → R) (t : B → B → R)
    (h : ∀ p q, bilOf c (t p) (t q) = linOf t (c' p q)) (x y : B → S) :
    bilOf (fun p q => φ ∘ c p q) (linOf (fun p => φ ∘ t p) x) (linOf (fun p => φ ∘ t p) y)
      = linOf (fun p => φ ∘ t p) (bilOf (fun p q => φ ∘ c' p q) x y) := by
  rw [bilOf_linOf, linOf_bilOf]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← map_bilOf, h, map_linOf]

/-- Composition of two maps given by columns. -/
theorem linOf_linOf (u t : B → B → R) (x : B → R) :
    linOf u (linOf t x) = linOf (fun p => linOf u (t p)) x := by
  funext k
  simp only [linOf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

theorem linOf_eB_cols [DecidableEq B] (x : B → R) : linOf (fun p => eB p) x = x := by
  funext k
  simp [linOf, eB, Finset.sum_apply]

end General
end OspOddDeformations
