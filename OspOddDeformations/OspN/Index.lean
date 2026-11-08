import OspOddDeformations.Bmn.Base

/-!
# The abstract fermion index, `FermionIndex`

Generalizes `Bmn`'s fixed `K m = Option (Fin m × Bool)` (odd `N = 2m+1` only) to an index type
that also covers even `N = 2m`: a structure packaging a finite, decidable-equality index type
with a self-dual involution and an injective sort key — exactly the two properties
`Bmn.dual`/`Bmn.KKey` are used for (`dual_dual`, `KKey_injective`); nothing else about `K m`'s
concrete shape is used by the base-bracket/`hTilde`/`Gamma`/`Cl` layer.

The namespace `OspOddDeformations.OspN` imports `Bmn` and leaves it unchanged.

The quadratic form of the Clifford algebra is used only in the general form
`QK x = BK x x = ½Σ_i x(i)x(dual i)` (`BK_apply`/`QK_apply` in `Source.lean`); the odd-`N`
form `x(none)² + Σ x(some(k,false))x(some(k,true))` has no even-`N` analogue (there is no
self-dual index when `N` is even). -/

namespace OspOddDeformations
namespace OspN

/-- A finite fermion index: a finite type with decidable equality, an involutive
"dual" pairing (`i* `, giving `g_{ij} = δ_{j,i*}`), and an injective `ℕ`-valued sort key
(the order used for `S_{ij}`, `i < j`). No other structure on the index is used anywhere in
the base-bracket, `hTilde`, `Gamma`, `delta`, or `Cl` layer. -/
structure FermionIndex where
  /-- The fermion index type. -/
  K : Type
  fin : Fintype K
  dec : DecidableEq K
  /-- The dual (self-)pairing, `i ↦ i*`. -/
  dual : K → K
  /-- `i** = i`. -/
  dual_dual : ∀ i, dual (dual i) = i
  /-- An injective sort key, giving the total order `S_{ij}` (`i < j`) is stated over. -/
  key : K → ℕ
  key_injective : Function.Injective key

attribute [instance] FermionIndex.fin FermionIndex.dec

/-- `g_{ij} = δ_{j,i*}`, for any `FermionIndex`: matches `Bmn.g` exactly at the odd
instance (`g_odd`, below). -/
def FermionIndex.g (F : FermionIndex) (i j : F.K) : ℚ := if j = F.dual i then 1 else 0

theorem FermionIndex.g_symm (F : FermionIndex) (i j : F.K) : F.g i j = F.g j i := by
  unfold FermionIndex.g
  by_cases h : j = F.dual i
  · have h2 : i = F.dual j := by rw [h, F.dual_dual]
    rw [ite_eq_left h, ite_eq_left h2]
  · have h2 : i ≠ F.dual j := fun hc => h (by rw [hc, F.dual_dual])
    rw [ite_eq_right h, ite_eq_right h2]

/-- **The odd instance**: `Bmn.K m`, `Bmn.dual m`, `Bmn.KKey`, reusing the existing
`Bmn` declarations directly (`Bmn.dual_dual`, `Bmn.KKey_injective`, in `Bmn/Base.lean`)
— no new proof, only repackaging. -/
noncomputable def oddIdx (m : ℕ) : FermionIndex where
  K := Bmn.K m
  fin := inferInstance
  dec := inferInstance
  dual := Bmn.dual m
  dual_dual := Bmn.dual_dual
  key := Bmn.KKey
  key_injective := fun {_ _} h => Bmn.KKey_injective h

/-- `g` at the odd instance is exactly `Bmn.g`. -/
theorem g_odd (m : ℕ) (i j : Bmn.K m) : (oddIdx m).g i j = Bmn.g m i j := rfl

/-- **The even instance**: `Fin m × Bool` (no `Option`, so no self-dual index — the
required property (`g` symmetric nondegenerate with `g_{i*,j} = δ_{ij}`) holds with the
*same* `dual`/`g` shape as the odd case, just without a `none` case), dual flips the
`Bool` (`(k,b)* = (k,¬b)`), key is the same `2k + (if b then 1 else 0)` shape as
`Bmn.KKey`'s `some`-case, shifted down by 1 (no `none` to reserve `0` for). -/
def evenIdx (m : ℕ) : FermionIndex where
  K := Fin m × Bool
  fin := inferInstance
  dec := inferInstance
  dual := fun (k, b) => (k, !b)
  dual_dual := by intro (k, b); simp
  key := fun (k, b) => 2 * k.val + (if b then 1 else 0)
  key_injective := by
    intro (k1, b1) (k2, b2) h
    simp only [Prod.mk.injEq]
    cases b1 <;> cases b2 <;> simp_all <;> omega

end OspN
end OspOddDeformations
