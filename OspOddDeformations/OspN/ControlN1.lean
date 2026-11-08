import OspOddDeformations.OspN.Identification
import OspOddDeformations.Bmn.Base
import InhomogeneousDeformations.IndexedCoboundary

/-!
# The `N = 1` control, against `osp-triviality`

At `oddIdx 0` (the odd instance with no fermion pair, `N = 1`, `osp(1|2n)`), `OspN`'s bracket, `Γ`,
`h̃` and `f_β` agree with `InhomogeneousDeformations`'s, under the evident transport of basis and
coefficient ring (`controlBasisEquivN1`, `controlRingEquivN1`, `controlTransportN1`). The modules
`InhomogeneousDeformations.*` are copies of the public `osp-triviality` (see
`InhomogeneousDeformations/PROVENANCE.md`), so a reader can check this against it.
-/

namespace OspOddDeformations
namespace OspN

open InhomogeneousDeformations
open Bmn (I K IKey J g dual index0nToFun index0nInvFun indexEquiv0n J_correspondence0n
  index0n_left_inv index0n_right_inv)

/-- `K 0 = Option (Fin 0 × Bool)` has exactly one inhabitant, `none`: `Fin 0`
is empty, so `some (k, b)` is impossible (`k : Fin 0`). -/
lemma k0_eq_none (i : K 0) : i = none := by
  cases i with
  | none => rfl
  | some p => exact p.1.elim0

@[simp] lemma IKey_index0nInvFun (n : ℕ) (j : Fin (2 * n)) :
    IKey (index0nInvFun n j) = j.val := by
  unfold index0nInvFun IKey
  by_cases h : j.val % 2 = 1 <;> simp [h] <;> omega

/-- `I n × K 0 ≃ I n`, since `K 0` is a singleton. -/
def indexProdN1 (n : ℕ) : I n × K 0 ≃ I n where
  toFun p := p.1
  invFun u := (u, none)
  left_inv p := by obtain ⟨u, i⟩ := p; rw [k0_eq_none i]
  right_inv _ := rfl

/-- The basis correspondence at `m = 0`: `S` is empty (`K 0` has one
element, so no `i < j`), `F` collapses to `I n` (`K 0` a singleton), and
`I n ≃ Fin (2n)` matches `Indexed.lean`'s own boson indexing exactly. -/
noncomputable def controlBasisEquivN1 (n : ℕ) : OspBasis (oddIdx 0) n ≃ Indexed.IndexedBasis n where
  toFun
    | .inl ⟨(u, v), h⟩ =>
        .inl ⟨(index0nToFun n u, index0nToFun n v), h⟩
    | .inr (.inl ⟨(i, j), h⟩) =>
        -- `K 0`'s singleton empties this subtype entirely: `KKey i = KKey j = 0`
        -- forces `h : 0 < 0`, absurd.
        absurd h (by rw [k0_eq_none i, k0_eq_none j]; simp)
    | .inr (.inr (u, _)) => .inr (index0nToFun n u)
  invFun
    | .inl ⟨(x, y), hxy⟩ =>
        .inl ⟨(index0nInvFun n x, index0nInvFun n y), by
          simp only [IKey_index0nInvFun]; exact hxy⟩
    | .inr x => .inr (.inr (index0nInvFun n x, none))
  left_inv := by
    intro a
    match a with
    | .inl ⟨(u, v), h⟩ =>
      have heq : (index0nInvFun n (index0nToFun n u), index0nInvFun n (index0nToFun n v))
          = (u, v) := by rw [index0n_left_inv n u, index0n_left_inv n v]
      simp only
      exact congrArg Sum.inl (Subtype.ext heq)
    | .inr (.inl ⟨(i, j), h⟩) => exact absurd h (by rw [k0_eq_none i, k0_eq_none j]; simp)
    | .inr (.inr (u, i)) =>
      simp only
      rw [k0_eq_none i, index0n_left_inv n u]
  right_inv := by
    intro b
    match b with
    | .inl ⟨(x, y), hxy⟩ =>
      have heq : (index0nToFun n (index0nInvFun n x), index0nToFun n (index0nInvFun n y))
          = (x, y) := by rw [index0n_right_inv n x, index0n_right_inv n y]
      simp only
      exact congrArg Sum.inl (Subtype.ext heq)
    | .inr x =>
      simp only
      rw [index0n_right_inv n x]

/-- The matching coefficient-ring isomorphism (`Pmn (oddIdx 0) n`'s generators
`I n × K 0` correspond to `Indexed.Pn n`'s generators `Fin (2n)`, via the
same `I n ≃ Fin (2n)`), built by `MvPolynomial.renameEquiv` from the index-level
`Equiv` `indexEquiv0n`. -/
noncomputable def controlRingEquivN1 (n : ℕ) : Pmn (oddIdx 0) n ≃+* Indexed.Pn n :=
  (MvPolynomial.renameEquiv ℚ ((indexProdN1 n).trans (indexEquiv0n n))).toRingEquiv

/-- Pushes a `OspMod (oddIdx 0) n` element forward to an `Indexed.IndexedMod n`
element along both correspondences. -/
noncomputable def controlTransportN1 {n : ℕ} (x : OspMod (oddIdx 0) n) : Indexed.IndexedMod n :=
  fun k => controlRingEquivN1 n (x ((controlBasisEquivN1 n).symm k))

lemma controlTransportN1_add (n : ℕ) (x y : OspMod (oddIdx 0) n) :
    controlTransportN1 (x + y) = controlTransportN1 (n := n) x + controlTransportN1 y := by
  funext k
  change controlRingEquivN1 n ((x + y) _) = controlRingEquivN1 n (x _) + controlRingEquivN1 n (y _)
  rw [ospMod_add_apply, map_add]

lemma controlTransportN1_neg (n : ℕ) (x : OspMod (oddIdx 0) n) :
    controlTransportN1 (-x) = -controlTransportN1 (n := n) x := by
  funext k
  change controlRingEquivN1 n ((-x) _) = -controlRingEquivN1 n (x _)
  rw [ospMod_neg_apply, map_neg]

lemma controlTransportN1_smul (n : ℕ) (c : ℚ) (x : OspMod (oddIdx 0) n) :
    controlTransportN1 (c • x) = c • controlTransportN1 (n := n) x := by
  funext k
  change (MvPolynomial.renameEquiv ℚ ((indexProdN1 n).trans (indexEquiv0n n))) (c • x _)
      = c • (MvPolynomial.renameEquiv ℚ ((indexProdN1 n).trans (indexEquiv0n n))) (x _)
  exact map_smul _ c _

lemma controlTransportN1_eN (n : ℕ) (Z : OspBasis (oddIdx 0) n) :
    controlTransportN1 (eN Z) = Indexed.eN (controlBasisEquivN1 n Z) := by
  funext k
  change controlRingEquivN1 n (eN Z ((controlBasisEquivN1 n).symm k)) = Indexed.eN _ k
  by_cases h : (controlBasisEquivN1 n).symm k = Z
  · have hk : k = controlBasisEquivN1 n Z := by rw [← h]; simp
    rw [eN, ite_eq_left h, hk, Indexed.eN, ite_eq_left rfl, map_one]
  · have hk : k ≠ controlBasisEquivN1 n Z := by
      intro hc; apply h; rw [hc]; simp
    rw [eN, ite_eq_right h, Indexed.eN, ite_eq_right hk, map_zero]

lemma qsmul_eq_Csmul_Pn {n : ℕ} (c : ℚ) (v : Indexed.IndexedMod n) :
    c • v = (MvPolynomial.C c : Indexed.Pn n) • v := by
  funext k
  simp [Algebra.smul_def]

/-- `Lof` transports to `Indexed.Lof`: both sort by the same condition
(`IKey a ≤ IKey b`, which is literally `index0nToFun n a ≤ index0nToFun n b`
in `Fin (2n)`'s order), so the same branch fires on both sides. -/
lemma controlBasisEquivN1_Lof (n : ℕ) (a b : I n) :
    controlBasisEquivN1 n (Lof a b) = Indexed.Lof (index0nToFun n a) (index0nToFun n b) := by
  unfold Lof Indexed.Lof
  by_cases h : IKey a ≤ IKey b
  · have h' : index0nToFun n a ≤ index0nToFun n b := h
    simp only [h, h', ↓reduceDIte]
    rfl
  · have h' : ¬ index0nToFun n a ≤ index0nToFun n b := h
    simp only [h, h', ↓reduceDIte]
    rfl

/-- `Fof` transports to `Indexed.Fof`, ignoring the (trivial, `K 0`) second
component. -/
lemma controlBasisEquivN1_Fof (n : ℕ) (a : I n) (i : K 0) :
    controlBasisEquivN1 n (Fof a i) = Indexed.Fof (index0nToFun n a) := rfl

/-- **Control, `(0,n)`, bracket**: `bracket0Basis` agrees with
`Indexed.bracketBasisN`. -/
theorem control_N1_bracket (n : ℕ) (X Y : OspBasis (oddIdx 0) n) :
    controlTransportN1 (bracket0Basis X Y)
      = Indexed.bracketBasisN n (controlBasisEquivN1 n X) (controlBasisEquivN1 n Y) := by
  match X, Y with
  | .inl ⟨(u, v), h⟩, .inl ⟨(w, z), h'⟩ =>
    change controlTransportN1 (bracketLL u v w z)
      = Indexed.bracketLLn n (index0nToFun n u) (index0nToFun n v) (index0nToFun n w)
          (index0nToFun n z)
    unfold bracketLL Indexed.bracketLLn
    rw [controlTransportN1_add, controlTransportN1_add, controlTransportN1_add,
        controlTransportN1_smul, controlTransportN1_smul, controlTransportN1_smul,
        controlTransportN1_smul,
        controlTransportN1_eN, controlTransportN1_eN, controlTransportN1_eN, controlTransportN1_eN,
        controlBasisEquivN1_Lof n v w, controlBasisEquivN1_Lof n u w, controlBasisEquivN1_Lof,
        controlBasisEquivN1_Lof,
        J_correspondence0n, J_correspondence0n, J_correspondence0n, J_correspondence0n]
    simp only [Indexed.cratN_mul]
    rw [qsmul_eq_Csmul_Pn, qsmul_eq_Csmul_Pn, qsmul_eq_Csmul_Pn, qsmul_eq_Csmul_Pn]
    unfold Indexed.cratN
    rfl
  | .inl _, .inr (.inl ⟨(i, j), h⟩) => exact absurd h (by rw [k0_eq_none i, k0_eq_none j]; simp)
  | .inl ⟨(u, v), h⟩, .inr (.inr (w, p)) =>
    change controlTransportN1 (bracketLF u v w p)
      = Indexed.bracketLFn n (index0nToFun n u) (index0nToFun n v) (index0nToFun n w)
    unfold bracketLF Indexed.bracketLFn
    rw [controlTransportN1_add, controlTransportN1_smul, controlTransportN1_smul,
        controlTransportN1_eN, controlTransportN1_eN,
        controlBasisEquivN1_Fof n u p, controlBasisEquivN1_Fof n v p,
        J_correspondence0n, J_correspondence0n]
    simp only [Indexed.cratN_mul]
    rw [qsmul_eq_Csmul_Pn, qsmul_eq_Csmul_Pn]
    unfold Indexed.cratN
    rfl
  | .inr (.inl ⟨(i, j), h⟩), .inl _ => exact absurd h (by rw [k0_eq_none i, k0_eq_none j]; simp)
  | .inr (.inl ⟨(i, j), h⟩), .inr (.inl ⟨(k, l), h'⟩) =>
    exact absurd h (by rw [k0_eq_none i, k0_eq_none j]; simp)
  | .inr (.inl ⟨(i, j), h⟩), .inr (.inr _) =>
    exact absurd h (by rw [k0_eq_none i, k0_eq_none j]; simp)
  | .inr (.inr (w, p)), .inl ⟨(u, v), h⟩ =>
    change controlTransportN1 (-bracketLF u v w p)
      = -Indexed.bracketLFn n (index0nToFun n u) (index0nToFun n v) (index0nToFun n w)
    rw [controlTransportN1_neg]
    congr 1
    unfold bracketLF Indexed.bracketLFn
    rw [controlTransportN1_add, controlTransportN1_smul, controlTransportN1_smul,
        controlTransportN1_eN, controlTransportN1_eN,
        controlBasisEquivN1_Fof n u p, controlBasisEquivN1_Fof n v p,
        J_correspondence0n, J_correspondence0n]
    simp only [Indexed.cratN_mul]
    rw [qsmul_eq_Csmul_Pn, qsmul_eq_Csmul_Pn]
    unfold Indexed.cratN
    rfl
  | .inr (.inr _), .inr (.inl ⟨(i, j), h⟩) =>
    exact absurd h (by rw [k0_eq_none i, k0_eq_none j]; simp)
  | .inr (.inr (u, p)), .inr (.inr (v, q)) =>
    change controlTransportN1 (bracketFF u p v q)
      = Indexed.bracketFFn n (index0nToFun n u) (index0nToFun n v)
    have hp : p = none := k0_eq_none p
    have hq : q = none := k0_eq_none q
    subst hp; subst hq
    unfold bracketFF Indexed.bracketFFn
    rw [show (Sof (none : K 0) none : OspMod (oddIdx 0) n) = 0 from by
          unfold Sof; rw [dite_eq_right (by simp), dite_eq_right (by simp)],
        smul_zero, zero_add,
        show ((oddIdx 0).g none none : ℚ) = 1 from by rw [g_odd]; unfold g dual; simp]
    rw [controlTransportN1_smul, controlTransportN1_eN, controlBasisEquivN1_Lof]
    rw [qsmul_eq_Csmul_Pn]
    unfold Indexed.cratN
    norm_num

lemma controlTransportN1_smul_ring (n : ℕ) (p : Pmn (oddIdx 0) n) (x : OspMod (oddIdx 0) n) :
    controlTransportN1 (p • x) = controlRingEquivN1 n p • controlTransportN1 (n := n) x := by
  funext k
  change controlRingEquivN1 n ((p • x) _) = controlRingEquivN1 n p * controlRingEquivN1 n (x _)
  rw [ospMod_smul_apply, map_mul]

/-- `beta` transports to `betaN`: `controlRingEquivN1` renames `X (u,i)`
along `(indexProdN1 n).trans (indexEquiv0n n)`, which sends `(u,i) ↦
index0nToFun n u` (dropping `K 0`'s trivial second slot). -/
lemma controlRingEquivN1_beta (n : ℕ) (u : I n) (i : K 0) :
    controlRingEquivN1 n (beta (oddIdx 0) n u i) = Indexed.betaN n (index0nToFun n u) := by
  change (MvPolynomial.renameEquiv ℚ ((indexProdN1 n).trans (indexEquiv0n n)))
      (MvPolynomial.X (u, i)) = Indexed.betaN n (index0nToFun n u)
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  rfl

/-- **Control, `(0,n)`, `Γ`**: `GammaBasis` agrees with
`IndexedCoboundary`'s `Γ` (`Indexed.GammaBetaBasis`). -/
theorem control_N1_gamma (n : ℕ) (X Y : OspBasis (oddIdx 0) n) :
    controlTransportN1 (GammaBasis X Y)
      = Indexed.GammaBetaBasis n (controlBasisEquivN1 n X) (controlBasisEquivN1 n Y) := by
  match X, Y with
  | .inl ⟨(u, v), h⟩, .inl ⟨(w, z), h'⟩ =>
    change controlTransportN1 (0 : OspMod (oddIdx 0) n) = (0 : Indexed.IndexedMod n)
    funext k; change controlRingEquivN1 n (0 : Pmn (oddIdx 0) n) = 0; rw [map_zero]
  | .inl _, .inr (.inl ⟨(i, j), h⟩) => exact absurd h (by rw [k0_eq_none i, k0_eq_none j]; simp)
  | .inl ⟨(u, v), h⟩, .inr (.inr (w, k)) =>
    change controlTransportN1 (GammaLF u v w k)
      = Indexed.gammaLFn n (index0nToFun n u) (index0nToFun n v) (index0nToFun n w)
    unfold GammaLF Indexed.gammaLFn
    rw [controlTransportN1_smul, controlTransportN1_add,
        controlTransportN1_smul_ring, controlTransportN1_smul_ring,
        controlTransportN1_eN, controlTransportN1_eN,
        controlBasisEquivN1_Lof n v w, controlBasisEquivN1_Lof n u w,
        controlRingEquivN1_beta n u k, controlRingEquivN1_beta n v k]
    rw [qsmul_eq_Csmul_Pn]
    unfold Indexed.cratN
    rfl
  | .inr (.inl ⟨(i, j), h⟩), .inl _ => exact absurd h (by rw [k0_eq_none i, k0_eq_none j]; simp)
  | .inr (.inl ⟨(i, j), h⟩), .inr (.inl ⟨(k, l), h'⟩) =>
    exact absurd h (by rw [k0_eq_none i, k0_eq_none j]; simp)
  | .inr (.inl ⟨(i, j), h⟩), .inr (.inr _) =>
    exact absurd h (by rw [k0_eq_none i, k0_eq_none j]; simp)
  | .inr (.inr (w, k)), .inl ⟨(u, v), h⟩ =>
    change controlTransportN1 (-GammaLF u v w k)
      = -Indexed.gammaLFn n (index0nToFun n u) (index0nToFun n v) (index0nToFun n w)
    rw [controlTransportN1_neg]
    congr 1
    unfold GammaLF Indexed.gammaLFn
    rw [controlTransportN1_smul, controlTransportN1_add,
        controlTransportN1_smul_ring, controlTransportN1_smul_ring,
        controlTransportN1_eN, controlTransportN1_eN,
        controlBasisEquivN1_Lof n v w, controlBasisEquivN1_Lof n u w,
        controlRingEquivN1_beta n u k, controlRingEquivN1_beta n v k]
    rw [qsmul_eq_Csmul_Pn]
    unfold Indexed.cratN
    rfl
  | .inr (.inr _), .inr (.inl ⟨(i, j), h⟩) =>
    exact absurd h (by rw [k0_eq_none i, k0_eq_none j]; simp)
  | .inr (.inr (u, p)), .inr (.inr (v, q)) =>
    have hp : p = none := k0_eq_none p
    have hq : q = none := k0_eq_none q
    subst hp; subst hq
    change controlTransportN1 (GammaFF u none v none)
      = Indexed.gammaFFn n (index0nToFun n u) (index0nToFun n v)
    unfold GammaFF Indexed.gammaFFn
    rw [controlTransportN1_smul, controlTransportN1_add,
        controlTransportN1_smul_ring, controlTransportN1_smul_ring,
        controlTransportN1_eN, controlTransportN1_eN,
        controlBasisEquivN1_Fof n u none, controlBasisEquivN1_Fof n v none,
        controlRingEquivN1_beta, controlRingEquivN1_beta]
    rw [qsmul_eq_Csmul_Pn]
    unfold Indexed.cratN
    rw [MvPolynomial.C_neg, neg_smul]

/-- `controlTransportN1` commutes with finite sums. -/
lemma controlTransportN1_sum (n : ℕ) {ι : Type*} (s : Finset ι) (f : ι → OspMod (oddIdx 0) n) :
    controlTransportN1 (∑ t ∈ s, f t) = ∑ t ∈ s, controlTransportN1 (f t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    funext k
    change controlRingEquivN1 n ((0 : OspMod (oddIdx 0) n) _) = 0
    rw [ospMod_zero_apply, map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, controlTransportN1_add, ih]

/-- `index0nToFun` on an even boson index is `Indexed.evenIdx`. -/
lemma idx_even_N1 (n : ℕ) (k : Fin n) : index0nToFun n (k, false) = Indexed.evenIdx n k := by
  apply Fin.ext; simp [index0nToFun, IKey, Indexed.evenIdx]

/-- `index0nToFun` on an odd boson index is `Indexed.oddIdx`. -/
lemma idx_odd_N1 (n : ℕ) (k : Fin n) : index0nToFun n (k, true) = Indexed.oddIdx n k := by
  apply Fin.ext; simp [index0nToFun, IKey, Indexed.oddIdx]

/-- **Control, `N = 1`, `h̃`**: `hTildeBasis` agrees with `Indexed.hBasis` (the map `h` of
arXiv:2604.05252, Section 3; `osp-triviality`'s `IndexedU.lean`). -/
theorem control_N1_hTilde (n : ℕ) (X : OspBasis (oddIdx 0) n) :
    controlTransportN1 (hTildeBasis X) = Indexed.hBasis n (controlBasisEquivN1 n X) := by
  match X with
  | .inl ⟨(u, v), h⟩ =>
    have hsum : (hTildeBasis (.inl ⟨(u, v), h⟩ : OspBasis (oddIdx 0) n) : OspMod (oddIdx 0) n)
        = beta (oddIdx 0) n u none • eN (Fof v none)
          + beta (oddIdx 0) n v none • eN (Fof u none) := by
      change (∑ i : (oddIdx 0).K, (beta (oddIdx 0) n u ((oddIdx 0).dual i) • eN (Fof v i)
          + beta (oddIdx 0) n v ((oddIdx 0).dual i) • eN (Fof u i))) = _
      refine (Finset.sum_eq_single (none : (oddIdx 0).K) ?_ ?_).trans ?_
      · intro i _ hi; exact absurd (k0_eq_none i) hi
      · intro h'; exact absurd (Finset.mem_univ _) h'
      · rfl
    rw [hsum, controlTransportN1_add, controlTransportN1_smul_ring, controlTransportN1_smul_ring,
      controlTransportN1_eN, controlTransportN1_eN, controlRingEquivN1_beta,
      controlRingEquivN1_beta]
    rfl
  | .inr (.inl ⟨(i, j), h⟩) => exact absurd h (by rw [k0_eq_none i, k0_eq_none j]; simp)
  | .inr (.inr (u, i)) =>
    have h0 : (hTildeBasis (.inr (.inr (u, i)) : OspBasis (oddIdx 0) n) : OspMod (oddIdx 0) n)
        = 0 := by
      change ((1 / 2 : ℚ) • ∑ j : (oddIdx 0).K,
        beta (oddIdx 0) n u j • Sof ((oddIdx 0).dual j) i) = 0
      have : ∀ j : (oddIdx 0).K, (Sof ((oddIdx 0).dual j) i : OspMod (oddIdx 0) n) = 0 := by
        intro j
        have hj : ((oddIdx 0).dual j) = none := k0_eq_none _
        have hi : i = none := k0_eq_none i
        rw [hj, hi]
        unfold Sof; rw [dite_eq_right (by simp), dite_eq_right (by simp)]
      simp [this]
    rw [h0]
    funext k
    change controlRingEquivN1 n ((0 : OspMod (oddIdx 0) n) _) = 0
    rw [ospMod_zero_apply, map_zero]

/-- **Control, `N = 1`, `f_β`**: `fBeta` on a basis element agrees with `Indexed.fBetaBasis` (the
primitive of arXiv:2604.05252, Theorem 4.1; `IndexedCoboundary.lean`). -/
theorem control_N1_fBeta (n : ℕ) (X : OspBasis (oddIdx 0) n) :
    controlTransportN1 (fBeta (oddIdx 0) n (eN X))
      = Indexed.fBetaBasis n (controlBasisEquivN1 n X) := by
  match X with
  | .inl ⟨(u, v), h⟩ =>
    have hL : (Sum.inl ⟨(u, v), h⟩ : OspBasis (oddIdx 0) n) = Lof u v :=
      (Lof_eq_sigma u v h).symm
    rw [hL, fBeta_L, controlBasisEquivN1_Lof, Indexed.fBetaBasis_Lof]
    funext k
    change controlRingEquivN1 n ((0 : OspMod (oddIdx 0) n) _) = 0
    rw [ospMod_zero_apply, map_zero]
  | .inr (.inl ⟨(i, j), h⟩) => exact absurd h (by rw [k0_eq_none i, k0_eq_none j]; simp)
  | .inr (.inr (w, i)) =>
    have hi : i = none := k0_eq_none i
    subst hi
    change controlTransportN1 (fBeta (oddIdx 0) n (eN (Fof w none)))
      = Indexed.fBetaBasis n (Indexed.Fof (index0nToFun n w))
    rw [fBeta_F (oddIdx 0) n w none, controlTransportN1_neg, controlTransportN1_sum]
    unfold Indexed.fBetaBasis
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have e1 : v (oddIdx 0) n (k, false) none = beta (oddIdx 0) n (k, true) none := rfl
    have e2 : v (oddIdx 0) n (k, true) none = -beta (oddIdx 0) n (k, false) none := rfl
    rw [e1, e2, controlTransportN1_smul_ring, controlTransportN1_smul_ring,
      controlTransportN1_eN, controlTransportN1_eN, controlBasisEquivN1_Lof,
      controlBasisEquivN1_Lof, map_neg, controlRingEquivN1_beta, controlRingEquivN1_beta,
      idx_even_N1, idx_odd_N1]
    simp only [neg_smul]
    abel


end OspN
end OspOddDeformations
