import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import InhomogeneousDeformations.Indexed

/-!
# `OspOddDeformations.Bmn.Base`

The declarations of `OspOddDeformations.Bmn` that `OspOddDeformations.OspN` uses, transitively,
taken unchanged from an earlier development for odd `N`: the boson and fermion index types and
their forms (`I`, `K`, `J`, `dual`, `g`, `IKey`, `KKey`), their laws, and the index correspondence
with `InhomogeneousDeformations.Indexed` used by `SourceTensor` and `SourceIndependence`.
-/

namespace OspOddDeformations
namespace Bmn

/-- The boson index `I n = {0,...,2n-1}`, structurally as `Fin n × Bool`:
`(k, false) = b_{2k}`, `(k, true) = b_{2k+1}`. -/
abbrev I (n : ℕ) : Type := Fin n × Bool

/-- The fermion index `K m = {0, 1+, 1-, ..., m+, m-}`, structurally as
`Option (Fin m × Bool)`: `none = a_0`, `some (k, false) = a_{k+}`,
`some (k, true) = a_{k-}`. -/
abbrev K (m : ℕ) : Type := Option (Fin m × Bool)

/-- The bosonic symplectic-type form: `J_{2k,2k+1} = 1`,
`J_{2k+1,2k} = -1`, zero otherwise. -/
def J (n : ℕ) : I n → I n → ℚ
  | (k1, false), (k2, true) => if k1 = k2 then 1 else 0
  | (k1, true), (k2, false) => if k1 = k2 then -1 else 0
  | _, _ => 0

/-- The fermion dual index `i*`: `0* = 0`, `k±* = k∓`. -/
def dual (m : ℕ) : K m → K m
  | none => none
  | some (k, b) => some (k, !b)

/-- The fermionic bilinear form: `g_{00} = 1`, `g_{k+,k-} =
g_{k-,k+} = 1`, zero otherwise; `g_{i,j} = 1 ↔ j = i*`. -/
def g (m : ℕ) (i j : K m) : ℚ := if j = dual m i then 1 else 0

/-- A total, decidable, injective-by-construction rank key on `I n`, used
only to decide `Lof`'s sort order — never claimed or needed to be a genuine
`LinearOrder`: this needs no injectivity or order-axiom proof, only
decidability of `≤` on `ℕ`. -/
def IKey {n : ℕ} (u : I n) : ℕ := 2 * u.1.val + (if u.2 then 1 else 0)

/-- The analogous rank key on `K m`, with `none` (i.e. `a_0`) ranked first. -/
def KKey {m : ℕ} : K m → ℕ
  | none => 0
  | some (k, b) => 2 * k.val + (if b then 1 else 0) + 1

theorem IKey_injective {n : ℕ} {u v : I n} (h : IKey u = IKey v) : u = v := by
  obtain ⟨a, ba⟩ := u
  obtain ⟨a', ba'⟩ := v
  simp only [IKey] at h
  have hab : a.val = a'.val ∧ ba = ba' := by
    cases ba <;> cases ba' <;> simp_all <;> omega
  exact Prod.ext (Fin.ext hab.1) hab.2

theorem dual_dual {m : ℕ} (i : K m) : dual m (dual m i) = i := by
  cases i with
  | none => rfl
  | some p => obtain ⟨k, b⟩ := p; simp [dual]

/-- `J` antisymmetry: `J_{vu} = -J_{uv}`, transposed from `Jn_antisymm`. -/
theorem J_antisymm {n : ℕ} (a b : I n) : J n a b = -J n b a := by
  obtain ⟨k1, b1⟩ := a
  obtain ⟨k2, b2⟩ := b
  cases b1 <;> cases b2 <;> simp only [J] <;> (try split_ifs) <;> simp_all

/-- `KKey`, mirrored from `IKey_injective`: the fermion analogue, needed to
turn "`Sof`'s dite falls to the zero branch" into "the two `K m` values
literally coincide" for `bracket0_S_Sof` below. -/
theorem KKey_injective {m : ℕ} {a b : K m} (h : KKey a = KKey b) : a = b := by
  match a, b with
  | none, none => rfl
  | none, some ⟨k, bb⟩ => simp only [KKey] at h; cases bb <;> omega
  | some ⟨k, bb⟩, none => simp only [KKey] at h; cases bb <;> omega
  | some ⟨k1, b1⟩, some ⟨k2, b2⟩ =>
    simp only [KKey] at h
    have hab : k1.val = k2.val ∧ b1 = b2 := by
      cases b1 <;> cases b2 <;> simp_all <;> omega
    exact congrArg some (Prod.ext (Fin.ext hab.1) hab.2)

open InhomogeneousDeformations

-- lint: the definition's text is kept identical to the original;
-- `unusedTactic` added in the Lean v4.35 port.
set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
/-- The `(0,n)` index map, `I n → Fin (2n)`: `(k,b) ↦ 2k + (b?1:0)`, exactly
`IKey`. -/
def index0nToFun (n : ℕ) (u : I n) : Fin (2 * n) :=
  ⟨IKey u, by
    obtain ⟨k, b⟩ := u
    have hk := k.isLt
    simp only [IKey]
    cases b <;> simp <;> omega⟩

/-- Its inverse, `j ↦ (j/2, j%2=1)`. -/
def index0nInvFun (n : ℕ) (j : Fin (2 * n)) : I n :=
  (⟨j.val / 2, by have hj := j.isLt; omega⟩, decide (j.val % 2 = 1))

/-- `left_inv`/`right_inv` of `indexEquiv0n`. -/
lemma index0n_left_inv (n : ℕ) : Function.LeftInverse (index0nInvFun n) (index0nToFun n) := by
  intro u
  obtain ⟨k, b⟩ := u
  unfold index0nInvFun index0nToFun IKey
  cases b <;> refine Prod.ext (Fin.ext ?_) ?_ <;> simp
  all_goals omega

lemma index0n_right_inv (n : ℕ) :
    Function.RightInverse (index0nInvFun n) (index0nToFun n) := by
  intro j
  apply Fin.ext
  unfold index0nToFun index0nInvFun IKey
  dsimp only
  by_cases h : j.val % 2 = 1 <;> simp [h] <;> omega

/-- The index correspondence at `m = 0`: `I n ≃ Fin (2n)`, matching
`Indexed.lean`'s own boson indexing exactly (the boson conventions here are
literally `osp-triviality`'s). -/
noncomputable def indexEquiv0n (n : ℕ) : I n ≃ Fin (2 * n) where
  toFun := index0nToFun n
  invFun := index0nInvFun n
  left_inv := index0n_left_inv n
  right_inv := index0n_right_inv n

-- lint (Lean v4.35 port): a `first`/`<;>` branch now reported unused; the text is kept.
set_option linter.unusedTactic false in
/-- The `J`/`Jn` correspondence under `index0nToFun`: matches `J`'s three
cases against `Jn`'s `%2`/`+1` conditions termwise. -/
lemma J_correspondence0n (n : ℕ) (a b : I n) :
    Indexed.Jn n (index0nToFun n a) (index0nToFun n b) = Indexed.cratN n (J n a b) := by
  obtain ⟨k1, b1⟩ := a
  obtain ⟨k2, b2⟩ := b
  cases b1 <;> cases b2 <;>
    simp only [J, index0nToFun, IKey] <;>
    unfold Indexed.Jn <;>
    (norm_num
      <;> split_ifs with hc1 hc2 <;>
        first
          | rfl
          | (exfalso; omega)
          | simp_all)

end Bmn
end OspOddDeformations
