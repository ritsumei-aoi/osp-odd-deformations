import OspOddDeformations.OspN.Coboundary

/-!
# The `κ` extension and `T`, for every `osp(N|2n)`

Paper Theorem 4.5 for a general `FermionIndex`: `T = id + κh̃_R` intertwines `[·,·]_β` with
`[·,·]₀` on `𝔤_R` (`intertwining`), with inverse `id − κh̃_R`. The sections follow
`osp-triviality`'s `IndexedKappa.lean`. Nothing here uses the concrete shape of the fermion index
(`RBasis`/`RMod` are built from `Bool`, not the fermion index at all); the substantive case of
`intertwining_basis` cites `Gamma_eq_delta_hTilde_basis` (`OspN/Coboundary.lean`).
-/

namespace OspOddDeformations
namespace OspN

/-! ## K0 -- the model `g_R = g_P ⊕ κg_P` -/

abbrev RBasis (F : FermionIndex) (n : ℕ) : Type := OspBasis F n × Bool

def parityR {F : FermionIndex} {n : ℕ} (p : RBasis F n) : ZMod 2 := parity p.1 +
  (if p.2 then 1 else 0)

abbrev RMod (F : FermionIndex) (n : ℕ) : Type := RBasis F n → Pmn F n

@[simp] lemma rMod_zero_apply {F : FermionIndex} {n : ℕ} (k : RBasis F n) :
  (0 : RMod F n) k = 0 := rfl
@[simp] lemma rMod_add_apply {F : FermionIndex} {n : ℕ} (x y : RMod F n) (k : RBasis F n) :
    (x + y) k = x k + y k := rfl
@[simp] lemma rMod_smul_apply {F : FermionIndex} {n : ℕ} (c : Pmn F n) (x : RMod F n)
  (k : RBasis F n) :
    (c • x) k = c * x k := rfl
@[simp] lemma rMod_neg_apply {F : FermionIndex} {n : ℕ} (x : RMod F n) (k : RBasis F n) : (-x)
  k = -x k := rfl

noncomputable def eR {F : FermionIndex} {n : ℕ} (b : RBasis F n) : RMod F n := fun k => if k =
  b then 1 else 0

/-- The embedding `ι_R : g_P → g_R`, into the `false` (un-scaled) slot. -/
noncomputable def iotaR {F : FermionIndex} {n : ℕ} (x : OspMod F n) : RMod F n := fun p => if p.2
  then 0 else x p.1

/-- `κ`-scaled embedding, directly into the `true` slot. -/
noncomputable def kappaEmbed {F : FermionIndex} {n : ℕ} (x : OspMod F n) : RMod F n :=
  fun p => if p.2 then x p.1 else 0

def falsePart {F : FermionIndex} {n : ℕ} (r : RMod F n) : OspMod F n := fun i => r (i, false)
def truePart {F : FermionIndex} {n : ℕ} (r : RMod F n) : OspMod F n := fun i => r (i, true)

@[simp] theorem falsePart_iotaR {F : FermionIndex} {n : ℕ} (x : OspMod F n) : falsePart
  (iotaR x) = x := by
  funext i; simp [falsePart, iotaR]

@[simp] theorem truePart_iotaR {F : FermionIndex} {n : ℕ} (x : OspMod F n) : truePart
  (iotaR x) = 0 := by
  funext i; simp [truePart, iotaR]

@[simp] theorem falsePart_kappaEmbed {F : FermionIndex} {n : ℕ} (x : OspMod F n) : falsePart
  (kappaEmbed x) = 0 := by
  funext i; simp [falsePart, kappaEmbed]

@[simp] theorem truePart_kappaEmbed {F : FermionIndex} {n : ℕ} (x : OspMod F n) : truePart
  (kappaEmbed x) = x := by
  funext i; simp [truePart, kappaEmbed]

theorem falsePart_add {F : FermionIndex} {n : ℕ} (r1 r2 : RMod F n) :
    falsePart (r1 + r2) = falsePart r1 + falsePart r2 := by funext i; simp [falsePart]

theorem falsePart_neg {F : FermionIndex} {n : ℕ} (r : RMod F n) : falsePart (-r) =
  -falsePart r := by
  funext i; simp [falsePart]

theorem falsePart_smul {F : FermionIndex} {n : ℕ} (c : Pmn F n) (r : RMod F n) :
    falsePart (c • r) = c • falsePart r := by funext i; simp [falsePart]

theorem iotaR_add {F : FermionIndex} {n : ℕ} (x y : OspMod F n) : iotaR (x + y) = iotaR x
  + iotaR y := by
  funext p; rcases p with ⟨i, b⟩; cases b <;> simp [iotaR]

theorem kappaEmbed_add {F : FermionIndex} {n : ℕ} (x y : OspMod F n) :
    kappaEmbed (x + y) = kappaEmbed x + kappaEmbed y := by
  funext p; rcases p with ⟨i, b⟩; cases b <;> simp [kappaEmbed]

theorem kappaEmbed_smul {F : FermionIndex} {n : ℕ} (c : Pmn F n) (x : OspMod F n) :
    kappaEmbed (c • x) = c • kappaEmbed x := by
  funext p; rcases p with ⟨i, b⟩; cases b <;> simp [kappaEmbed]

theorem kappaEmbed_zero (F : FermionIndex) (n : ℕ) : kappaEmbed (0 : OspMod F n) =
  (0 : RMod F n) := by
  funext p; rcases p with ⟨i, b⟩; cases b <;> simp [kappaEmbed]

theorem kappaEmbed_sum {F : FermionIndex} {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → OspMod F n) :
    kappaEmbed (∑ i ∈ s, f i) = ∑ i ∈ s, kappaEmbed (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [kappaEmbed_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, kappaEmbed_add, ih, Finset.sum_insert ha]

theorem kappaEmbed_sum_smul {F : FermionIndex} {n : ℕ} {ι : Type*} (s : Finset ι) (c : ι → Pmn F n)
    (f : ι → OspMod F n) :
    kappaEmbed (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • kappaEmbed (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [kappaEmbed_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, kappaEmbed_add, kappaEmbed_smul, ih, Finset.sum_insert ha]

/-- `ℚ`-scalar version of `kappaEmbed_smul`: `gsign (...)`-style coefficients
are `ℚ`-valued, not `Pmn F n`-valued, so this is a genuinely separate lemma
(not a special case), mirroring `Coboundary.lean`'s own `hTilde_smul` /
`hTilde_smul_rat` pair. -/
theorem kappaEmbed_smul_rat {F : FermionIndex} {n : ℕ} (c : ℚ) (x : OspMod F n) :
    kappaEmbed (c • x) = c • kappaEmbed x := by
  funext p; rcases p with ⟨i, b⟩; cases b <;> simp [kappaEmbed]

theorem kappaEmbed_sum_smul_rat {F : FermionIndex} {n : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℚ)
    (f : ι → OspMod F n) :
    kappaEmbed (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • kappaEmbed (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [kappaEmbed_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, kappaEmbed_add, kappaEmbed_smul_rat, ih, Finset.sum_insert ha]

/-- `κ`-multiplication on `g_R`: `κ * (x0 + κx1) = κx0`. -/
noncomputable def kappaMulR {F : FermionIndex} {n : ℕ} (r : RMod F n) : RMod F n :=
  fun p => if p.2 then r (p.1, false) else 0

theorem kappaMulR_add {F : FermionIndex} {n : ℕ} (r1 r2 : RMod F n) :
    kappaMulR (r1 + r2) = kappaMulR r1 + kappaMulR r2 := by
  funext p; rcases p with ⟨i, b⟩; cases b <;> simp [kappaMulR]

theorem kappaMulR_iotaR {F : FermionIndex} {n : ℕ} (x : OspMod F n) : kappaMulR (iotaR x) =
  kappaEmbed x := by
  funext p; rcases p with ⟨i, b⟩; cases b <;> simp [kappaMulR, iotaR, kappaEmbed]

theorem kappaMulR_kappaEmbed {F : FermionIndex} {n : ℕ} (x : OspMod F n) : kappaMulR
  (kappaEmbed x) = 0 := by
  funext p; rcases p with ⟨i, b⟩; cases b <;> simp [kappaMulR, kappaEmbed]

theorem sum_bool_eq {M : Type*} [AddCommMonoid M] (f : Bool → M) :
    ∑ b : Bool, f b = f true + f false := by
  rw [Fintype.univ_bool, Finset.sum_insert (by decide), Finset.sum_singleton]

/-! ## K1 -- the extended undeformed bracket, `[rX,sY]₀ = (-1)^{p(X)p(s)}rs[X,Y]₀` -/

noncomputable def bracketRBasis {F : FermionIndex} {n : ℕ} : RBasis F n → RBasis F n → RMod F n
  | (i, false), (j, false) => iotaR (bracket0Basis i j)
  | (i, false), (j, true) => kappaEmbed (gsign (parity i) 1 • bracket0Basis i j)
  | (i, true), (j, false) => kappaEmbed (bracket0Basis i j)
  | (_, true), (_, true) => 0

noncomputable def bracketR {F : FermionIndex} {n : ℕ} (x y : RMod F n) : RMod F n :=
  ∑ p : RBasis F n, ∑ q : RBasis F n, (x p * y q) • bracketRBasis p q

theorem bracketR_eR_eR {F : FermionIndex} {n : ℕ} (p q : RBasis F n) :
    bracketR (eR p) (eR q) = bracketRBasis p q := by
  unfold bracketR
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · simp [eR]
    · intro b _ hb
      have : eR q b = 0 := by unfold eR; rw [ite_eq_right hb]
      simp [this]
    · intro h; exact absurd (Finset.mem_univ q) h
  · intro b _ hb
    have : eR p b = 0 := by unfold eR; rw [ite_eq_right hb]
    simp [this]
  · intro h; exact absurd (Finset.mem_univ p) h

theorem bracketR_zero_left {F : FermionIndex} {n : ℕ} (y : RMod F n) : bracketR
  (0 : RMod F n) y = 0 := by
  unfold bracketR; simp

theorem bracketR_zero_right {F : FermionIndex} {n : ℕ} (x : RMod F n) : bracketR x
  (0 : RMod F n) = 0 := by
  unfold bracketR; simp

theorem bracketR_add_left {F : FermionIndex} {n : ℕ} (x1 x2 y : RMod F n) :
    bracketR (x1 + x2) y = bracketR x1 y + bracketR x2 y := by
  unfold bracketR
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro p _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro q _
  simp only [rMod_add_apply]
  rw [add_mul, add_smul]

theorem bracketR_add_right {F : FermionIndex} {n : ℕ} (x y1 y2 : RMod F n) :
    bracketR x (y1 + y2) = bracketR x y1 + bracketR x y2 := by
  unfold bracketR
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro p _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro q _
  simp only [rMod_add_apply]
  rw [mul_add, add_smul]

theorem bracketR_smul_left {F : FermionIndex} {n : ℕ} (c : Pmn F n) (x y : RMod F n) :
    bracketR (c • x) y = c • bracketR x y := by
  unfold bracketR
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl; intro q _
  simp only [rMod_smul_apply, smul_smul]
  congr 1; ring

theorem bracketR_smul_right {F : FermionIndex} {n : ℕ} (c : Pmn F n) (x y : RMod F n) :
    bracketR x (c • y) = c • bracketR x y := by
  unfold bracketR
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl; intro q _
  simp only [rMod_smul_apply, smul_smul]
  congr 1; ring

theorem bracketR_eR_left {F : FermionIndex} {n : ℕ} (p : RBasis F n) (x : RMod F n) :
    bracketR (eR p) x = ∑ q : RBasis F n, x q • bracketRBasis p q := by
  unfold bracketR
  rw [Finset.sum_eq_single p]
  · apply Finset.sum_congr rfl; intro q _; simp [eR]
  · intro b _ hb
    have : eR p b = 0 := by unfold eR; rw [ite_eq_right hb]
    simp [this]
  · intro h; exact absurd (Finset.mem_univ p) h

theorem bracketR_eR_right {F : FermionIndex} {n : ℕ} (x : RMod F n) (q : RBasis F n) :
    bracketR x (eR q) = ∑ p : RBasis F n, x p • bracketRBasis p q := by
  unfold bracketR
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.sum_eq_single q]
  · simp [eR]
  · intro b _ hb
    have : eR q b = 0 := by unfold eR; rw [ite_eq_right hb]
    simp [this]
  · intro h; exact absurd (Finset.mem_univ q) h

-- the instance argument is part of the published signature; it is used only through `classical` in
-- the proof
set_option linter.unusedDecidableInType false in
theorem bracketR_sum_left' {F : FermionIndex} {n : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
  (f : ι → RMod F n)
    (y : RMod F n) : bracketR (∑ i ∈ s, f i) y = ∑ i ∈ s, bracketR (f i) y := by
  induction s using Finset.induction with
  | empty => simp [bracketR_zero_left]
  | @insert a s ha ih => rw [Finset.sum_insert ha, bracketR_add_left, ih, Finset.sum_insert ha]

-- the instance argument is part of the published signature; it is used only through `classical` in
-- the proof
set_option linter.unusedDecidableInType false in
theorem bracketR_sum_right' {F : FermionIndex} {n : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
  (f : ι → RMod F n)
    (x : RMod F n) : bracketR x (∑ i ∈ s, f i) = ∑ i ∈ s, bracketR x (f i) := by
  induction s using Finset.induction with
  | empty => simp [bracketR_zero_right]
  | @insert a s ha ih => rw [Finset.sum_insert ha, bracketR_add_right, ih, Finset.sum_insert ha]

-- the instance argument is part of the published signature; it is used only through `classical` in
-- the proof
set_option linter.unusedDecidableInType false in
theorem bracketR_sum_left'' {F : FermionIndex} {n : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
  (c : ι → Pmn F n)
    (f : ι → RMod F n) (y : RMod F n) :
    bracketR (∑ i ∈ s, c i • f i) y = ∑ i ∈ s, c i • bracketR (f i) y := by
  induction s using Finset.induction with
  | empty => simp [bracketR_zero_left]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, bracketR_add_left, bracketR_smul_left, ih, Finset.sum_insert ha]

-- the instance argument is part of the published signature; it is used only through `classical` in
-- the proof
set_option linter.unusedDecidableInType false in
theorem bracketR_sum_right'' {F : FermionIndex} {n : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
  (c : ι → Pmn F n)
    (f : ι → RMod F n) (x : RMod F n) :
    bracketR x (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • bracketR x (f i) := by
  induction s using Finset.induction with
  | empty => simp [bracketR_zero_right]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, bracketR_add_right, bracketR_smul_right, ih, Finset.sum_insert ha]

theorem eR_decompose {F : FermionIndex} {n : ℕ} (r : RMod F n) : r = ∑ p : RBasis F n,
  r p • eR p := by
  funext l
  rw [Finset.sum_apply]
  simp only [rMod_smul_apply]
  rw [Finset.sum_eq_single l]
  · simp [eR]
  · intro k _ hk
    have : eR k l = 0 := by unfold eR; rw [ite_eq_right (Ne.symm hk)]
    simp [this]
  · intro h; exact absurd (Finset.mem_univ l) h

theorem kappaEmbed_eq_sum {F : FermionIndex} {n : ℕ} (y : OspMod F n) :
    kappaEmbed y = ∑ k : OspBasis F n, y k • eR ((k, true) : RBasis F n) := by
  funext p; rcases p with ⟨l, b⟩
  rw [Finset.sum_apply]
  simp only [rMod_smul_apply]
  rw [Finset.sum_eq_single l]
  · simp [eR, kappaEmbed]
  · intro k _ hk
    have : eR ((k, true) : RBasis F n) (l, b) = 0 := by
      unfold eR
      rw [ite_eq_right (fun h => hk (congrArg Prod.fst h).symm)]
    simp [this]
  · intro h; exact absurd (Finset.mem_univ l) h

theorem bracketR_eR_false_kappaEmbed {F : FermionIndex} {n : ℕ} (i : OspBasis F n)
  (y : OspMod F n) :
    bracketR (eR ((i, false) : RBasis F n)) (kappaEmbed y)
      = kappaEmbed (gsign (parity i) 1 • bracket0 (eN i) y) := by
  have hlhs : bracketR (eR ((i, false) : RBasis F n)) (kappaEmbed y)
      = ∑ k : OspBasis F n, y k • kappaEmbed (gsign (parity i) 1 • bracket0Basis i k) := by
    rw [bracketR_eR_left]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro k _
    rw [sum_bool_eq]
    have h1 : (kappaEmbed y (k, false)) •
        bracketRBasis ((i, false) : RBasis F n) (k, false) = 0 := by
      simp [kappaEmbed]
    rw [h1, add_zero]
    change (kappaEmbed y (k, true)) • bracketRBasis ((i, false) : RBasis F n) (k, true)
      = (y k) • kappaEmbed (gsign (parity i) 1 • bracket0Basis i k)
    simp [kappaEmbed, bracketRBasis]
  rw [hlhs, bracket0_eN_left, Finset.smul_sum, kappaEmbed_sum_smul_rat]
  apply Finset.sum_congr rfl; intro k _
  rw [kappaEmbed_smul_rat, kappaEmbed_smul]
  exact smul_comm (y k) (gsign (parity i) 1) (kappaEmbed (bracket0Basis i k))

theorem bracketR_kappaEmbed_eR_false {F : FermionIndex} {n : ℕ} (y : OspMod F n)
  (j : OspBasis F n) :
    bracketR (kappaEmbed y) (eR ((j, false) : RBasis F n)) = kappaEmbed (bracket0 y (eN j)) := by
  rw [kappaEmbed_eq_sum, bracketR_sum_left']
  have hstep : ∀ k : OspBasis F n,
      bracketR (y k • eR ((k, true) : RBasis F n)) (eR ((j, false) : RBasis F n))
      = y k • kappaEmbed (bracket0Basis k j) := by
    intro k
    rw [bracketR_smul_left, bracketR_eR_eR]
    rfl
  rw [Finset.sum_congr rfl (fun k _ => hstep k), bracket0_eN_right, kappaEmbed_sum_smul]

theorem bracketR_eR_true_kappaEmbed {F : FermionIndex} {n : ℕ} (i : OspBasis F n) (y : OspMod F n) :
    bracketR (eR ((i, true) : RBasis F n)) (kappaEmbed y) = 0 := by
  rw [kappaEmbed_eq_sum, bracketR_sum_right']
  apply Finset.sum_eq_zero; intro k _
  rw [bracketR_smul_right, bracketR_eR_eR]
  simp [bracketRBasis]

theorem bracketR_kappaEmbed_eR_true {F : FermionIndex} {n : ℕ} (y : OspMod F n) (j : OspBasis F n) :
    bracketR (kappaEmbed y) (eR ((j, true) : RBasis F n)) = 0 := by
  rw [kappaEmbed_eq_sum, bracketR_sum_left']
  apply Finset.sum_eq_zero; intro k _
  rw [bracketR_smul_left, bracketR_eR_eR]
  simp [bracketRBasis]

theorem bracketR_kappaEmbed_kappaEmbed {F : FermionIndex} {n : ℕ} (y1 y2 : OspMod F n) :
    bracketR (kappaEmbed y1) (kappaEmbed y2) = 0 := by
  rw [kappaEmbed_eq_sum y1 (F := F) (n := n), bracketR_sum_left']
  apply Finset.sum_eq_zero; intro k _
  rw [bracketR_smul_left, bracketR_eR_true_kappaEmbed]
  simp

theorem falsePart_eR_false {F : FermionIndex} {n : ℕ} (i : OspBasis F n) :
    falsePart ((eR ((i, false) : RBasis F n))) = eN i := by
  funext k
  unfold falsePart eR eN
  simp [Prod.ext_iff]

theorem falsePart_eR_true {F : FermionIndex} {n : ℕ} (i : OspBasis F n) :
    falsePart ((eR ((i, true) : RBasis F n))) = 0 := by
  funext k
  unfold falsePart eR
  simp

/-! ## K2 -- the odd `R`-linear extension `h̃_R`, `hTilde` for `fBetaN` -/

noncomputable def hTildeR {F : FermionIndex} {n : ℕ} (r : RMod F n) : RMod F n :=
  iotaR (hTilde (falsePart r)) + kappaEmbed (-(hTilde (truePart r)))

/-! ## K3 -- `T` and its inverse, `T = id + κh̃_R` (paper Theorem 4.5; Lean `TBeta`) -/

noncomputable def TBeta {F : FermionIndex} {n : ℕ} (r : RMod F n) : RMod F n := r +
  kappaMulR (hTildeR r)

noncomputable def TBetaInv {F : FermionIndex} {n : ℕ} (r : RMod F n) : RMod F n := r -
  kappaMulR (hTildeR r)

theorem TBeta_eq {F : FermionIndex} {n : ℕ} (r : RMod F n) : TBeta r = r + kappaEmbed
  (hTilde (falsePart r)) := by
  unfold TBeta hTildeR
  rw [kappaMulR_add, kappaMulR_iotaR, kappaMulR_kappaEmbed, add_zero]

theorem TBetaInv_eq {F : FermionIndex} {n : ℕ} (r : RMod F n) :
    TBetaInv r = r - kappaEmbed (hTilde (falsePart r)) := by
  unfold TBetaInv hTildeR
  rw [kappaMulR_add, kappaMulR_iotaR, kappaMulR_kappaEmbed, add_zero]

theorem falsePart_TBeta {F : FermionIndex} {n : ℕ} (r : RMod F n) : falsePart (TBeta r) =
  falsePart r := by
  rw [TBeta_eq, falsePart_add, falsePart_kappaEmbed, add_zero]

theorem falsePart_TBetaInv {F : FermionIndex} {n : ℕ} (r : RMod F n) : falsePart (TBetaInv r) =
  falsePart r := by
  rw [TBetaInv_eq, sub_eq_add_neg, falsePart_add, falsePart_neg, falsePart_kappaEmbed, neg_zero,
    add_zero]

/-- `T` and `T⁻¹` are mutually inverse, exactly, for
arbitrary `r : g_R`. -/
theorem TBetaInv_TBeta {F : FermionIndex} {n : ℕ} (r : RMod F n) : TBetaInv (TBeta r) = r := by
  rw [TBetaInv_eq, falsePart_TBeta, TBeta_eq]
  abel

theorem TBeta_TBetaInv {F : FermionIndex} {n : ℕ} (r : RMod F n) : TBeta (TBetaInv r) = r := by
  rw [TBeta_eq, falsePart_TBetaInv, TBetaInv_eq]
  abel

theorem TBeta_zero {F : FermionIndex} {n : ℕ} : TBeta (0 : RMod F n) = 0 := by
  have hfp0 : falsePart (0 : RMod F n) = 0 := by funext k; simp [falsePart]
  rw [TBeta_eq, hfp0, hTilde_zero, kappaEmbed_zero, add_zero]

theorem TBeta_add {F : FermionIndex} {n : ℕ} (r1 r2 : RMod F n) : TBeta (r1 + r2) = TBeta r1
  + TBeta r2 := by
  rw [TBeta_eq, TBeta_eq, TBeta_eq, falsePart_add, hTilde_add, kappaEmbed_add]
  abel

theorem TBeta_smul {F : FermionIndex} {n : ℕ} (c : Pmn F n) (r : RMod F n) : TBeta (c • r) = c
  • TBeta r := by
  rw [TBeta_eq, TBeta_eq, falsePart_smul, hTilde_smul, kappaEmbed_smul, smul_add]

-- the instance argument is part of the published signature; it is used only through `classical` in
-- the proof
set_option linter.unusedDecidableInType false in
theorem TBeta_sum {F : FermionIndex} {n : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
  (f : ι → RMod F n) :
    TBeta (∑ i ∈ s, f i) = ∑ i ∈ s, TBeta (f i) := by
  induction s using Finset.induction with
  | empty => simp [TBeta_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, TBeta_add, ih, Finset.sum_insert ha]

-- the instance argument is part of the published signature; it is used only through `classical` in
-- the proof
set_option linter.unusedDecidableInType false in
theorem TBeta_sum' {F : FermionIndex} {n : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
  (c : ι → Pmn F n)
    (f : ι → RMod F n) :
    TBeta (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • TBeta (f i) := by
  induction s using Finset.induction with
  | empty => simp [TBeta_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, TBeta_add, TBeta_smul, ih, Finset.sum_insert ha]

theorem TBeta_eR_false {F : FermionIndex} {n : ℕ} (i : OspBasis F n) :
    TBeta (eR ((i, false) : RBasis F n))
      = eR ((i, false) : RBasis F n) + kappaEmbed (hTildeBasis i) := by
  rw [TBeta_eq, falsePart_eR_false, hTilde_eN]

theorem TBeta_eR_true {F : FermionIndex} {n : ℕ} (i : OspBasis F n) :
    TBeta (eR ((i, true) : RBasis F n)) = eR ((i, true) : RBasis F n) := by
  rw [TBeta_eq, falsePart_eR_true, hTilde_zero, kappaEmbed_zero, add_zero]

/-! ## K4 -- the deformed bracket, `[X,Y]_β = [X,Y]₀ + κΓ_β(X,Y)` -/

noncomputable def bracketRBetaBasis {F : FermionIndex} {n : ℕ} : RBasis F n → RBasis F n → RMod F n
  | (i, false), (j, false) => iotaR (bracket0Basis i j) + kappaEmbed (GammaBasis i j)
  | (i, false), (j, true) => kappaEmbed (gsign (parity i) 1 • bracket0Basis i j)
  | (i, true), (j, false) => kappaEmbed (bracket0Basis i j)
  | (_, true), (_, true) => 0

noncomputable def bracketRBeta {F : FermionIndex} {n : ℕ} (x y : RMod F n) : RMod F n :=
  ∑ p : RBasis F n, ∑ q : RBasis F n, (x p * y q) • bracketRBetaBasis p q

theorem bracketRBeta_eR_eR {F : FermionIndex} {n : ℕ} (p q : RBasis F n) :
    bracketRBeta (eR p) (eR q) = bracketRBetaBasis p q := by
  unfold bracketRBeta
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · simp [eR]
    · intro b _ hb
      have : eR q b = 0 := by unfold eR; rw [ite_eq_right hb]
      simp [this]
    · intro h; exact absurd (Finset.mem_univ q) h
  · intro b _ hb
    have : eR p b = 0 := by unfold eR; rw [ite_eq_right hb]
    simp [this]
  · intro h; exact absurd (Finset.mem_univ p) h

/-! ## K5 -- the intertwining -/

/-- **The intertwining**, basis level: it holds on every basis pair,
citing `Γ_β = δh̃` (`Gamma_eq_delta_hTilde_basis`) in the substantive `(false,false)` case,
as `osp-triviality`'s `IndexedKappa.lean` cites its `G4`. -/
theorem intertwining_basis {F : FermionIndex} {n : ℕ} (p q : RBasis F n) :
    bracketR (TBeta (eR p)) (TBeta (eR q)) = TBeta (bracketRBeta (eR p) (eR q)) := by
  rcases p with ⟨i, bi⟩; rcases q with ⟨j, bj⟩
  cases bi <;> cases bj
  · -- (i,false),(j,false) -- the substantive case
    rw [TBeta_eR_false, TBeta_eR_false, bracketRBeta_eR_eR]
    show bracketR (eR ((i, false) : RBasis F n) + kappaEmbed (hTildeBasis i))
        (eR ((j, false) : RBasis F n) + kappaEmbed (hTildeBasis j))
      = TBeta (bracketRBetaBasis (i, false) (j, false))
    rw [bracketR_add_left, bracketR_add_right, bracketR_add_right]
    rw [bracketR_eR_eR, bracketR_eR_false_kappaEmbed, bracketR_kappaEmbed_eR_false,
        bracketR_kappaEmbed_kappaEmbed, add_zero]
    simp only [bracketRBasis]
    set A := gsign (parity i) 1 • bracket0 (eN i) (hTildeBasis j) with hA
    set B := bracket0 (hTildeBasis i) (eN j) with hB
    have hfix : TBeta (kappaEmbed (GammaBasis i j)) = kappaEmbed (GammaBasis i j) := by
      rw [TBeta_eq, falsePart_kappaEmbed, hTilde_zero, kappaEmbed_zero, add_zero]
    simp only [bracketRBetaBasis]
    rw [TBeta_add, TBeta_eq, falsePart_iotaR, hfix]
    set Z := hTilde (bracket0Basis i j) with hZ
    rw [Gamma_eq_delta_hTilde_basis]
    unfold deltaBasis
    rw [bracket0_eN_eN, hTilde_eN, hTilde_eN, ← hB, ← hA, ← hZ]
    have key : kappaEmbed A + kappaEmbed B = kappaEmbed Z + kappaEmbed (B + A - Z) := by
      rw [← kappaEmbed_add, ← kappaEmbed_add]
      congr 1
      abel
    calc iotaR (bracket0Basis i j) + kappaEmbed A + kappaEmbed B
        = iotaR (bracket0Basis i j) + (kappaEmbed A + kappaEmbed B) := by abel
      _ = iotaR (bracket0Basis i j) + (kappaEmbed Z + kappaEmbed (B + A - Z)) := by rw [key]
      _ = iotaR (bracket0Basis i j) + kappaEmbed Z + kappaEmbed (B + A - Z) := by abel
  · -- (i,false),(j,true)
    rw [TBeta_eR_false, TBeta_eR_true, bracketRBeta_eR_eR]
    show bracketR (eR ((i, false) : RBasis F n) + kappaEmbed (hTildeBasis i))
        (eR ((j, true) : RBasis F n))
      = TBeta (bracketRBetaBasis (i, false) (j, true))
    rw [bracketR_add_left, bracketR_eR_eR, bracketR_kappaEmbed_eR_true, add_zero]
    show bracketRBasis (i, false) (j, true) = TBeta (bracketRBetaBasis (i, false) (j, true))
    change kappaEmbed (gsign (parity i) 1 • bracket0Basis i j)
      = TBeta (kappaEmbed (gsign (parity i) 1 • bracket0Basis i j))
    rw [TBeta_eq, falsePart_kappaEmbed, hTilde_zero, kappaEmbed_zero, add_zero]
  · -- (i,true),(j,false)
    rw [TBeta_eR_true, TBeta_eR_false, bracketRBeta_eR_eR]
    show bracketR (eR ((i, true) : RBasis F n))
        (eR ((j, false) : RBasis F n) + kappaEmbed (hTildeBasis j))
      = TBeta (bracketRBetaBasis (i, true) (j, false))
    rw [bracketR_add_right, bracketR_eR_eR, bracketR_eR_true_kappaEmbed, add_zero]
    show bracketRBasis (i, true) (j, false) = TBeta (bracketRBetaBasis (i, true) (j, false))
    change kappaEmbed (bracket0Basis i j) = TBeta (kappaEmbed (bracket0Basis i j))
    rw [TBeta_eq, falsePart_kappaEmbed, hTilde_zero, kappaEmbed_zero, add_zero]
  · -- (i,true),(j,true)
    rw [TBeta_eR_true, TBeta_eR_true, bracketRBeta_eR_eR, bracketR_eR_eR]
    change (0 : RMod F n) = TBeta (0 : RMod F n)
    rw [TBeta_zero]

/-- **The intertwining** `[TX,TY]₀=T([X,Y]_β)`, for
**arbitrary** (not just homogeneous) elements. -/
theorem intertwining {F : FermionIndex} {n : ℕ} (x y : RMod F n) :
    bracketR (TBeta x) (TBeta y) = TBeta (bracketRBeta x y) := by
  have hLHS : bracketR (TBeta x) (TBeta y)
      = ∑ p : RBasis F n, ∑ q : RBasis F n,
          (x p * y q) • bracketR (TBeta (eR p)) (TBeta (eR q)) := by
    conv_lhs => rw [eR_decompose x, eR_decompose y]
    rw [TBeta_sum', TBeta_sum', bracketR_sum_left'']
    apply Finset.sum_congr rfl; intro p _
    rw [bracketR_sum_right'', Finset.smul_sum]
    apply Finset.sum_congr rfl; intro q _
    rw [smul_smul]
  have hRHS : TBeta (bracketRBeta x y)
      = ∑ p : RBasis F n, ∑ q : RBasis F n,
          (x p * y q) • bracketR (TBeta (eR p)) (TBeta (eR q)) := by
    unfold bracketRBeta
    rw [TBeta_sum]
    apply Finset.sum_congr rfl; intro p _
    rw [TBeta_sum']
    apply Finset.sum_congr rfl; intro q _
    rw [← bracketRBeta_eR_eR p q]
    exact congrArg (fun z => (x p * y q) • z) (intertwining_basis p q).symm
  rw [hLHS, hRHS]

end OspN
end OspOddDeformations
