import OspOddDeformations.OspN.FBeta

/-!
# The identification `𝔤 ≅ osp(M,𝓑)`, for every `osp(N|2n)`

Paper Proposition 3.4: `M` (indexed by `Sum F.K (I n)`), `𝓑`, `ospCond`, and `ρ`. Mathlib has no Lie
superalgebras, so `M`'s "vectors" are represented the same way `𝔤`'s own coordinate module is
(`Midx F n → ℚ`, an index type paired with a plain function-module), and `ρ` is given basis
element by basis element, exactly as `bracket0Basis` is.

The data (`Midx`, `pM`, `Bform`, `Bpair`, `ospCond`, `rhoBasis`) transcribe the paper's
formulas. Proved: `ρ` lands in `osp(M,𝓑)` (`rho_ospCond`), preserves brackets (`rho_bracket`),
is injective (`rhoBasis_linearIndependent`), and has every homogeneous element of `osp(M,𝓑)` in
its image (`rho_span`). -/

-- Toolchain port (v4.34): `OspBasis` is a plain `def` whose sum structure the proofs use; restore
-- the pre-v4.34 type-transparency behaviour of `isDefEq` for this file.
set_option backward.isDefEq.respectTransparency.types false


namespace OspOddDeformations
namespace OspN

open Bmn (I J J_antisymm IKey IKey_injective)

/-- `M`'s index type: even `e_i` (`i : F.K`), odd `e_u` (`u : I n`) — parities are the
*reverse* of `𝔤`'s own (`a_i` odd, `b_u` even), per the paper's own `π`. -/
def Midx (F : FermionIndex) (n : ℕ) : Type := F.K ⊕ I n

instance (F : FermionIndex) (n : ℕ) : Fintype (Midx F n) := by unfold Midx; infer_instance
noncomputable instance (F : FermionIndex) (n : ℕ) : DecidableEq (Midx F n) := Classical.decEq _

/-- `M`'s parity: `0` on the even (`F.K`) part, `1` on the odd (`I n`) part. -/
def pM {F : FermionIndex} {n : ℕ} : Midx F n → ZMod 2
  | .inl _ => 0
  | .inr _ => 1

noncomputable abbrev MMod (F : FermionIndex) (n : ℕ) : Type := Midx F n → ℚ

noncomputable def eNM {F : FermionIndex} {n : ℕ} (i : Midx F n) : MMod F n :=
  fun k => if k = i then 1 else 0

/-- `𝓑(e_i,e_k) = -g_{ik}`, `𝓑(e_u,e_w) = J_{uw}`, mixed values `0` (paper Prop.
3.4). -/
def Bform {F : FermionIndex} {n : ℕ} : Midx F n → Midx F n → ℚ
  | .inl i, .inl k => -(F.g i k)
  | .inl _, .inr _ => 0
  | .inr _, .inl _ => 0
  | .inr u, .inr w => J n u w

/-- `𝓑`'s bilinear extension to `MMod F n`. -/
noncomputable def Bpair {F : FermionIndex} {n : ℕ} (x y : MMod F n) : ℚ :=
  ∑ i : Midx F n, ∑ j : Midx F n, x i * y j * Bform i j

/-- The `osp(M,𝓑)` condition for a homogeneous, basis-given endomorphism `Tb` of parity
`p`: `𝓑(Tb i, e_j) + (-1)^{p·p_M(i)}𝓑(e_i, Tb j) = 0` for all basis `i, j`
(`OspN.gsign p q` computes `(-1)^{p∧q}`, i.e. `(-1)^{pq}` for `p,q ∈ ZMod 2` — matches
`Bmn.Bracket.gsign`, reused here without redefinition). -/
def ospCond {F : FermionIndex} {n : ℕ} (p : ZMod 2) (Tb : Midx F n → MMod F n) : Prop :=
  ∀ i j : Midx F n, Bpair (Tb i) (eNM j) + gsign p (pM i) • Bpair (eNM i) (Tb j) = 0

/-- `ρ(L_{uv})`, `ρ(S_{ij})`, `ρ(F_{u,i})`, one basis-to-`MMod` map per lift kind, from
`bracket0Basis`'s own three-way split. -/
noncomputable def rhoBasis {F : FermionIndex} {n : ℕ} :
    OspBasis F n → Midx F n → MMod F n
  | .inl ⟨(u, v), _⟩ => fun m => match m with
      | .inl _ => 0
      | .inr w => (1 / 2 : ℚ) • (J n v w • eNM (.inr u) + J n u w • eNM (.inr v))
  | .inr (.inl ⟨(i, j), _⟩) => fun m => match m with
      | .inl k => F.g j k • eNM (.inl i) - F.g i k • eNM (.inl j)
      | .inr _ => 0
  | .inr (.inr (u, i)) => fun m => match m with
      | .inl k => (1 / 2 : ℚ) • (F.g i k • eNM (.inr u))
      | .inr w => (1 / 2 : ℚ) • (J n u w • eNM (.inl i))

/-- `ρ(X)`, `rhoBasis X`'s linear extension to `MMod F n → MMod F n`. -/
noncomputable def rhoOp {F : FermionIndex} {n : ℕ} (X : OspBasis F n) (m : MMod F n) :
    MMod F n := fun j => ∑ i : Midx F n, m i * rhoBasis X i j

/-- `bracket0Basis`'s coefficients are always rational constants (no `β` ever appears —
checked directly against `OspN/Bracket.lean`: every term is `J`, `F.g`, or `1/2`/`1/4`),
so this reads off that constant, letting bracket-preservation be stated as an identity
of `MMod`-valued (i.e. `ℚ`-coefficient) maps, matching `Bform`'s own `ℚ`-valued type. -/
noncomputable def bracket0BasisQ {F : FermionIndex} {n : ℕ} (X Y k : OspBasis F n) : ℚ :=
  MvPolynomial.constantCoeff (bracket0Basis X Y k)

/-! ## `bracket0Basis_const`'s own toolkit: `IsConstAt`, a closure predicate

`bracket0Basis X Y` is, in every one of its nine kinds, built from only `eN`/`Sof`/`0`
combined by ℚ-`smul`/`+`/`-`/`neg` — never a genuine polynomial (no `β` ever appears).
`IsConstAt p k` states `p k` is `algebraMap` of some `ℚ`; it is closed under exactly
those five operations, so a single generic combinator tactic (`repeat' first | apply
... | exact isConstAt_eN .. | ...`) closes every one of the nine `bracket0Basis` kinds
uniformly, with no case-split on `k` needed at all. -/

theorem eN_eq_algebraMap {F : FermionIndex} {n : ℕ} (Z k : OspBasis F n) :
    eN Z k = algebraMap ℚ (Pmn F n) (if k = Z then (1 : ℚ) else 0) := by
  unfold eN; split_ifs with h <;> simp

theorem algebraMap_smul_eq {F : FermionIndex} {n : ℕ} (c1 c2 : ℚ) :
    c1 • (algebraMap ℚ (Pmn F n) c2 : Pmn F n) = algebraMap ℚ (Pmn F n) (c1 * c2) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul]

def IsConstAt {F : FermionIndex} {n : ℕ} (p : OspMod F n) (k : OspBasis F n) : Prop :=
  ∃ c : ℚ, p k = algebraMap ℚ (Pmn F n) c

theorem isConstAt_zero {F : FermionIndex} {n : ℕ} (k : OspBasis F n) :
    IsConstAt (0 : OspMod F n) k := ⟨0, by simp⟩

theorem isConstAt_eN {F : FermionIndex} {n : ℕ} (Z k : OspBasis F n) :
    IsConstAt (eN Z : OspMod F n) k := ⟨_, eN_eq_algebraMap Z k⟩

theorem isConstAt_add {F : FermionIndex} {n : ℕ} (p q : OspMod F n) (k : OspBasis F n)
    (hp : IsConstAt p k) (hq : IsConstAt q k) : IsConstAt (p + q) k := by
  obtain ⟨c1, h1⟩ := hp; obtain ⟨c2, h2⟩ := hq
  exact ⟨c1 + c2, by rw [ospMod_add_apply, h1, h2, map_add]⟩

theorem isConstAt_neg {F : FermionIndex} {n : ℕ} (p : OspMod F n) (k : OspBasis F n)
    (hp : IsConstAt p k) : IsConstAt (-p) k := by
  obtain ⟨c, h⟩ := hp
  exact ⟨-c, by rw [ospMod_neg_apply, h, map_neg]⟩

theorem isConstAt_sub {F : FermionIndex} {n : ℕ} (p q : OspMod F n) (k : OspBasis F n)
    (hp : IsConstAt p k) (hq : IsConstAt q k) : IsConstAt (p - q) k := by
  rw [sub_eq_add_neg]; exact isConstAt_add p (-q) k hp (isConstAt_neg q k hq)

theorem isConstAt_smul {F : FermionIndex} {n : ℕ} (c1 : ℚ) (p : OspMod F n) (k : OspBasis F n)
    (hp : IsConstAt p k) : IsConstAt (c1 • p) k := by
  obtain ⟨c2, h2⟩ := hp
  exact ⟨c1 * c2, by rw [Pi.smul_apply, h2, algebraMap_smul_eq]⟩

theorem isConstAt_Sof {F : FermionIndex} {n : ℕ} (i j : F.K) (k : OspBasis F n) :
    IsConstAt (Sof i j : OspMod F n) k := by
  unfold Sof
  split_ifs
  · exact isConstAt_eN _ k
  · exact isConstAt_neg _ k (isConstAt_eN _ k)
  · exact isConstAt_zero k

theorem isConstAt_to_algebraMap {F : FermionIndex} {n : ℕ} (p : OspMod F n) (k : OspBasis F n)
    (h : IsConstAt p k) :
    p k = algebraMap ℚ (Pmn F n) (MvPolynomial.constantCoeff (p k)) := by
  obtain ⟨c, hc⟩ := h
  rw [hc]; congr 1; simp

-- lint (Lean v4.35 port): a `first`/`<;>` branch now reported unused; the text is kept.
set_option linter.unusedTactic false in
/-- `bracket0Basis` really is `algebraMap ℚ (Pmn F n)` of its own extracted constant — the
link `rho_bracket` needs to reach the actual `bracket0Basis` (`Pmn`-valued), not
merely its own derived `ℚ`-constant. Proved via the `IsConstAt` toolkit above: matches
`bracket0Basis`'s own nine-kind match exactly, unfolding each branch's `bracketLL`/
`bracketSS`/`bracketLF`/`bracketSF`/`bracketFF`/`0`/`neg` shape and closing uniformly
with the generic combinator. -/
theorem bracket0Basis_const {F : FermionIndex} {n : ℕ} (X Y k : OspBasis F n) :
    bracket0Basis X Y k = algebraMap ℚ (Pmn F n) (bracket0BasisQ X Y k) := by
  unfold bracket0BasisQ
  apply isConstAt_to_algebraMap
  unfold bracket0Basis
  match X, Y with
  | .inl ⟨(u, v), _⟩, .inl ⟨(w, z), _⟩ =>
    change IsConstAt (bracketLL u v w z) k
    unfold bracketLL
    repeat' first
      | apply isConstAt_add | apply isConstAt_sub | apply isConstAt_smul | apply isConstAt_neg
      | exact isConstAt_Sof _ _ k | exact isConstAt_eN _ k
  | .inl _, .inr (.inl _) => exact isConstAt_zero k
  | .inl ⟨(u, v), _⟩, .inr (.inr (w, i)) =>
    change IsConstAt (bracketLF u v w i) k
    unfold bracketLF
    repeat' first
      | apply isConstAt_add | apply isConstAt_sub | apply isConstAt_smul | apply isConstAt_neg
      | exact isConstAt_Sof _ _ k | exact isConstAt_eN _ k
  | .inr (.inl _), .inl _ => exact isConstAt_zero k
  | .inr (.inl ⟨(i, j), _⟩), .inr (.inl ⟨(l, m), _⟩) =>
    change IsConstAt (bracketSS i j l m) k
    unfold bracketSS
    repeat' first
      | apply isConstAt_add | apply isConstAt_sub | apply isConstAt_smul | apply isConstAt_neg
      | exact isConstAt_Sof _ _ k
  | .inr (.inl ⟨(j, l), _⟩), .inr (.inr (w, i)) =>
    change IsConstAt (bracketSF j l w i) k
    unfold bracketSF
    repeat' first
      | apply isConstAt_add | apply isConstAt_sub | apply isConstAt_smul | apply isConstAt_neg
      | exact isConstAt_Sof _ _ k | exact isConstAt_eN _ k
  | .inr (.inr (w, i)), .inl ⟨(u, v), _⟩ =>
    change IsConstAt (-bracketLF u v w i) k
    unfold bracketLF
    repeat' first
      | apply isConstAt_add | apply isConstAt_sub | apply isConstAt_smul | apply isConstAt_neg
      | exact isConstAt_Sof _ _ k | exact isConstAt_eN _ k
  | .inr (.inr (w, i)), .inr (.inl ⟨(j, l), _⟩) =>
    change IsConstAt (-bracketSF j l w i) k
    unfold bracketSF
    repeat' first
      | apply isConstAt_add | apply isConstAt_sub | apply isConstAt_smul | apply isConstAt_neg
      | exact isConstAt_Sof _ _ k | exact isConstAt_eN _ k
  | .inr (.inr (u, i)), .inr (.inr (v, j)) =>
    change IsConstAt (bracketFF u i v j) k
    unfold bracketFF
    repeat' first
      | apply isConstAt_add | apply isConstAt_sub | apply isConstAt_smul | apply isConstAt_neg
      | exact isConstAt_Sof _ _ k | exact isConstAt_eN _ k

/-! ## `rho_ospCond`'s own toolkit: `Bpair`'s bilinearity, `eNM`-collapse, `gsign` -/

theorem Bpair_eNM_eNM {F : FermionIndex} {n : ℕ} (i j : Midx F n) :
    Bpair (eNM i : MMod F n) (eNM j) = Bform i j := by
  unfold Bpair eNM
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem Bpair_add_left {F : FermionIndex} {n : ℕ} (x y z : MMod F n) :
    Bpair (x + y) z = Bpair x z + Bpair y z := by
  unfold Bpair
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  simp [add_mul]

theorem Bpair_smul_left {F : FermionIndex} {n : ℕ} (c : ℚ) (x y : MMod F n) :
    Bpair (c • x) y = c * Bpair x y := by
  unfold Bpair
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  simp [mul_assoc]

theorem Bpair_zero_left {F : FermionIndex} {n : ℕ} (y : MMod F n) :
    Bpair (0 : MMod F n) y = 0 := by unfold Bpair; simp

theorem Bpair_add_right {F : FermionIndex} {n : ℕ} (x y z : MMod F n) :
    Bpair x (y + z) = Bpair x y + Bpair x z := by
  unfold Bpair
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  simp [mul_add]; ring

theorem Bpair_smul_right {F : FermionIndex} {n : ℕ} (c : ℚ) (x y : MMod F n) :
    Bpair x (c • y) = c * Bpair x y := by
  unfold Bpair
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  simp; ring

theorem Bpair_zero_right {F : FermionIndex} {n : ℕ} (x : MMod F n) :
    Bpair x (0 : MMod F n) = 0 := by unfold Bpair; simp

theorem Bpair_neg_left {F : FermionIndex} {n : ℕ} (x y : MMod F n) :
    Bpair (-x) y = -Bpair x y := by unfold Bpair; simp

theorem Bpair_neg_right {F : FermionIndex} {n : ℕ} (x y : MMod F n) :
    Bpair x (-y) = -Bpair x y := by unfold Bpair; simp

theorem Bpair_sub_left {F : FermionIndex} {n : ℕ} (x y z : MMod F n) :
    Bpair (x - y) z = Bpair x z - Bpair y z := by
  rw [sub_eq_add_neg, Bpair_add_left, Bpair_neg_left, sub_eq_add_neg]

theorem Bpair_sub_right {F : FermionIndex} {n : ℕ} (x y z : MMod F n) :
    Bpair x (y - z) = Bpair x y - Bpair x z := by
  rw [sub_eq_add_neg, Bpair_add_right, Bpair_neg_right, sub_eq_add_neg]

theorem gsign_zero_left (q : ZMod 2) : gsign (0 : ZMod 2) q = 1 := by unfold gsign; simp

/-- **`ρ` lands in `osp(M,𝓑)`** (paper Prop. 3.4, part "the image lies in
`osp`"). Splits on `X`'s own kind (`L`/`S`/`F`, matching `rhoBasis`'s own three-way
match), then on `i,j`'s own even/odd `Midx` kind (four sub-cases each): `Bform`'s mixed
(even-odd) values are always `0`, and `rhoBasis`'s own output is supported only at the
"wrong" parity for its OWN kind's non-matching input branch (`L`/`S`'s even/odd-only
support, `F`'s swapped support) — so three of the four `i,j` sub-cases per kind vanish
by pure `ring` bookkeeping once `Bform`/`rhoBasis` are unfolded, and the remaining
"generic" sub-case per kind closes by a single application of `F.g_symm` (`L`, `S`) or
`J_antisymm` (`L` twice, `F`), matching the by-hand check of the paper's proof. -/
theorem rho_ospCond {F : FermionIndex} {n : ℕ} (X : OspBasis F n) :
    ospCond (parity X) (rhoBasis X) := by
  match X with
  | .inl ⟨(u, v), huv⟩ =>
    change ospCond (0 : ZMod 2) (rhoBasis (Sum.inl ⟨(u, v), huv⟩ : OspBasis F n))
    intro p q
    rw [gsign_zero_left, one_smul]
    rcases p with k1 | t <;> rcases q with k2 | w <;>
      simp only [rhoBasis, Bpair_zero_left, Bpair_zero_right, Bpair_add_left, Bpair_add_right,
        Bpair_smul_left, Bpair_smul_right, Bpair_eNM_eNM, add_zero, zero_add, Bform]
    · ring
    · ring
    · rw [J_antisymm t u, J_antisymm t v]; ring
  | .inr (.inl ⟨(i, j), hij⟩) =>
    change ospCond (0 : ZMod 2) (rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n))
    intro p q
    rw [gsign_zero_left, one_smul]
    rcases p with k1 | t <;> rcases q with k2 | w <;>
      simp only [rhoBasis, Bpair_zero_left, Bpair_zero_right,
        Bpair_smul_left, Bpair_smul_right, Bpair_sub_left, Bpair_sub_right, Bpair_eNM_eNM,
        add_zero, zero_add, Bform]
    · rw [F.g_symm k1 i, F.g_symm k1 j]; ring
    · ring
    · ring
  | .inr (.inr (u, i)) =>
    change ospCond (1 : ZMod 2) (rhoBasis (Sum.inr (Sum.inr (u, i)) : OspBasis F n))
    intro p q
    rcases p with k1 | t <;> rcases q with k2 | w <;>
      simp only [rhoBasis, pM, gsign_10, gsign_11, one_smul, neg_one_smul,
        Bpair_smul_left, Bpair_smul_right,
        Bpair_eNM_eNM, Bform]
    · ring
    · rw [F.g_symm k1 i]; ring
    · rw [J_antisymm t u]; ring
    · ring

/-! ## `rhoBasis_linearIndependent`'s own toolkit -- L-kind coefficient extraction

The route: evaluate `Σc_X• ρ(X)` at chosen vectors to extract each
coefficient. `Fintype.linearIndependent_iff` reduces the goal to: `∀ c, (Σc_X•ρ(X) = 0)
→ ∀X, c X = 0`; for each `X`, evaluate the hypothesis at a SPECIFIC `(input,
output-component)` pair chosen so every OTHER basis element's own contribution vanishes
there, isolating `c X` (up to a known nonzero factor). `L_indep_full` below does this
for `L`-kind `X = L_{u0,v0}`: evaluating at input `inr (v0.1,!v0.2)` (`v0`'s own `J`-dual
partner) and reading the `inr u0` output-component. `S`-kind and `F`-kind extraction
follow further below (`S_indep_full`, `F_indep_full`), mirroring this same route.
`Fintype.sum_sum_type` (applied twice, `OspBasis F n` being a three-way `Sum`) splits
`Σ_X` into its `L`/`S`/`F` parts; within the `L`-part, `Finset.sum_eq_single` isolates
the target pair, using `L_indep_other` to show every OTHER valid `L`-pair contributes
`0` -- the one genuinely delicate step, since `L`-kind's own `bracketLL` formula mixes
`u,v` symmetrically (unlike `S`/`F`), needing `IKey_injective` to rule out the "reversed
pair" `(v0,u0)` as a spurious contributor when it happens to also be valid. -/

theorem eNM_I_eq {F : FermionIndex} {n : ℕ} (Z k : I n) :
    (eNM (Sum.inr Z) : MMod F n) (Sum.inr k) = if k = Z then (1 : ℚ) else 0 := by
  unfold eNM
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (Sum.inr.inj_iff.mp h1) h2
  · exact absurd (by rw [h2]) h1
  · rfl

theorem J_diag_ne_zero (n : ℕ) (k0 : Fin n) (b0 : Bool) (u0 : I n) :
    ((J n ((k0, b0) : I n) (k0, !b0) * if u0 = u0 then (1 : ℚ) else 0)
      + J n u0 (k0, !b0) * if u0 = (k0, b0) then (1 : ℚ) else 0) ≠ 0 := by
  simp only
  obtain ⟨ku, bu⟩ := u0
  cases b0 <;> cases bu <;> simp_all [J] <;> split_ifs <;> norm_num

/-- Every `L`-kind pair OTHER than the target `(u0,v0)` contributes `0` to the
`(inr u0)`-component of `bracketLL`'s own `rhoBasis` value, evaluated at
`inr (v0.1,!v0.2)`: `J`'s own single-nonzero-match property (`J n a b ≠ 0 → b = a`'s
own `Fin`-partner with flipped `Bool`) picks out at most the target pair itself in
each of `bracketLL`'s two terms, and `IKey_injective` rules out the "reversed pair"
`(v0,u0)` as a spurious second match (it would force `u0=v0`, collapsing back to the
target). -/
theorem L_indep_other (F : FermionIndex) (n : ℕ) (u0 v0 u' v' : I n)
    (huv0 : IKey u0 ≤ IKey v0) (huv' : IKey u' ≤ IKey v')
    (hne : (⟨(u', v'), huv'⟩ : {p : I n × I n // IKey p.1 ≤ IKey p.2})
        ≠ ⟨(u0, v0), huv0⟩) :
    (1 / 2 : ℚ) * (J n v' (v0.1, !v0.2) * ((eNM (Sum.inr u') : MMod F n) (Sum.inr u0))
      + J n u' (v0.1, !v0.2) * ((eNM (Sum.inr v') : MMod F n) (Sum.inr u0))) = 0 := by
  rw [eNM_I_eq, eNM_I_eq]
  have hpne : (u', v') ≠ (u0, v0) := fun h => hne (by rw [Subtype.mk.injEq]; exact h)
  obtain ⟨k0, b0⟩ := v0
  obtain ⟨ku, bu'⟩ := u'
  obtain ⟨kv, bv'⟩ := v'
  simp only [J] at *
  rcases b0 with _ | _ <;> rcases bu' with _ | _ <;> rcases bv' with _ | _ <;>
    [ simp_all only [ne_eq, Subtype.mk.injEq, not_false_eq_true, Prod.mk.injEq, and_true, not_and,
          one_div, Bool.not_false, mul_ite, ↓reduceIte, mul_one, mul_zero, ite_self, zero_add,
          ite_eq_right_iff, inv_eq_zero, OfNat.ofNat_ne_zero, imp_false]
    ; simp_all only [ne_eq, Subtype.mk.injEq, not_false_eq_true, Prod.mk.injEq, Bool.true_eq_false,
          and_false, one_div, Bool.not_false, mul_ite, mul_one, mul_zero, ite_self, zero_add,
          ite_eq_right_iff, inv_eq_zero, OfNat.ofNat_ne_zero, imp_false]
    ; simp_all only [ne_eq, Subtype.mk.injEq, not_false_eq_true, Prod.mk.injEq, and_true, not_and,
          one_div, Bool.not_false, mul_ite, ↓reduceIte, mul_one, mul_zero, ite_self, add_zero]
    ; simp_all only [ne_eq, Subtype.mk.injEq, not_false_eq_true, Prod.mk.injEq, Bool.true_eq_false,
          and_false, one_div, Bool.not_false, mul_ite, mul_one, mul_zero, ite_self, add_zero]
    ; simp_all only [ne_eq, Subtype.mk.injEq, not_false_eq_true, Prod.mk.injEq, Bool.false_eq_true,
          and_false, one_div, Bool.not_true, mul_ite, mul_one, mul_zero, ite_self, add_zero]
    ; simp_all only [ne_eq, Subtype.mk.injEq, not_false_eq_true, Prod.mk.injEq, and_true, not_and,
          one_div, Bool.not_true, mul_ite, ↓reduceIte, mul_one, mul_zero, ite_self, add_zero]
    ; simp_all only [ne_eq, Subtype.mk.injEq, not_false_eq_true, Prod.mk.injEq, Bool.false_eq_true,
          and_false, one_div, Bool.not_true, mul_ite, mul_one, mul_zero, ite_self,
            zero_add, mul_neg,
          ite_eq_right_iff, neg_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, imp_false]
    ; simp_all only [ne_eq, Subtype.mk.injEq, not_false_eq_true, Prod.mk.injEq, and_true, not_and,
          one_div, Bool.not_true, mul_ite, ↓reduceIte, mul_one, mul_zero, ite_self,
            zero_add, mul_neg,
          ite_eq_right_iff, neg_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, imp_false]
    ]
  · intro h hcon
    have hu0v0 : (kv, false) = (k0, false) :=
      h.symm ▸ IKey_injective (le_antisymm huv0 (by rw [h, ← hcon]; exact huv'))
    have hk : kv = k0 := (Prod.ext_iff.mp hu0v0).1
    exact hpne (by rw [hcon, ← hk]; exact h.symm) hk
  · intro h hcon
    have hu0v0 : (kv, true) = (k0, false) :=
      h.symm ▸ IKey_injective (le_antisymm huv0 (by rw [h, ← hcon]; exact huv'))
    simp at hu0v0
  · intro h hcon
    have hu0v0 : (kv, false) = (k0, true) :=
      h.symm ▸ IKey_injective (le_antisymm huv0 (by rw [h, ← hcon]; exact huv'))
    simp at hu0v0
  · intro h hcon
    have hu0v0 : (kv, true) = (k0, true) :=
      h.symm ▸ IKey_injective (le_antisymm huv0 (by rw [h, ← hcon]; exact huv'))
    have hk : kv = k0 := (Prod.ext_iff.mp hu0v0).1
    exact hpne (by rw [hcon, ← hk]; exact h.symm) hk

/-- **The `L`-kind case of `rhoBasis_linearIndependent`**: if `Σc_X•ρ(X) = 0`, the
coefficient of any `L`-kind basis pair `(u0,v0)` is `0`. Splits `Σ_X` into its `L`/`S`/
`F` parts (`Fintype.sum_sum_type`, twice); the `S`,`F` parts vanish entirely at this
evaluation point (`hS`,`hFp` — `S`-kind sends odd input to `0`, `F`-kind sends odd
input to an `inl`-supported value, both missing the `inr u0` component read off here);
the `L`-part collapses via `Finset.sum_eq_single` and `L_indep_other`, landing on
`J_diag_ne_zero`'s own nonzero coefficient. -/
theorem L_indep_full (F : FermionIndex) (n : ℕ) (c : OspBasis F n → ℚ)
    (hc : ∑ X : OspBasis F n, c X • rhoBasis X = 0)
    (u0 v0 : I n) (huv0 : IKey u0 ≤ IKey v0) :
    c (Sum.inl ⟨(u0, v0), huv0⟩ : OspBasis F n) = 0 := by
  have h1 := congrFun (congrFun hc (Sum.inr (v0.1, !v0.2))) (Sum.inr u0)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
  rw [show (0 : Midx F n → MMod F n) (Sum.inr (v0.1, !v0.2)) (Sum.inr u0) = (0 : ℚ) from rfl] at h1
  have hsplit1 : (∑ X : OspBasis F n, c X * rhoBasis X (Sum.inr (v0.1, !v0.2)) (Sum.inr u0))
      = ∑ a : {p : I n × I n // IKey p.1 ≤ IKey p.2},
          c (Sum.inl a) * rhoBasis (Sum.inl a) (Sum.inr (v0.1, !v0.2)) (Sum.inr u0)
        + ∑ b : ({p : F.K × F.K // F.key p.1 < F.key p.2} ⊕ (I n × F.K)),
          c (Sum.inr b) * rhoBasis (Sum.inr b) (Sum.inr (v0.1, !v0.2)) (Sum.inr u0) :=
    Fintype.sum_sum_type (fun X => c X * rhoBasis X (Sum.inr (v0.1, !v0.2)) (Sum.inr u0))
  rw [hsplit1] at h1
  have hsplit2 : (∑ b : ({p : F.K × F.K // F.key p.1 < F.key p.2} ⊕ (I n × F.K)),
        c (Sum.inr b) * rhoBasis (Sum.inr b : OspBasis F n) (Sum.inr (v0.1, !v0.2)) (Sum.inr u0))
      = ∑ Y : {p : F.K × F.K // F.key p.1 < F.key p.2},
          c (Sum.inr (Sum.inl Y))
            * rhoBasis (Sum.inr (Sum.inl Y) : OspBasis F n) (Sum.inr (v0.1, !v0.2)) (Sum.inr u0)
        + ∑ Z : I n × F.K,
          c (Sum.inr (Sum.inr Z))
            * rhoBasis (Sum.inr (Sum.inr Z) : OspBasis F n) (Sum.inr (v0.1, !v0.2)) (Sum.inr u0) :=
    Fintype.sum_sum_type
      (fun b => c (Sum.inr b) * rhoBasis (Sum.inr b : OspBasis F n)
        (Sum.inr (v0.1, !v0.2)) (Sum.inr u0))
  rw [hsplit2] at h1
  have hS : ∀ X : {p : F.K × F.K // F.key p.1 < F.key p.2},
      c (Sum.inr (Sum.inl X) : OspBasis F n)
        * rhoBasis (Sum.inr (Sum.inl X) : OspBasis F n) (Sum.inr (v0.1, !v0.2))
          (Sum.inr u0) = 0 := by
    intro X
    obtain ⟨⟨i, j⟩, hij⟩ := X
    show c _ * (rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n)
        (Sum.inr (v0.1, !v0.2)) : MMod F n) (Sum.inr u0) = 0
    simp only [rhoBasis]
    rw [show (0 : MMod F n) (Sum.inr u0) = (0 : ℚ) from rfl, mul_zero]
  have hFp : ∀ X : I n × F.K,
      c (Sum.inr (Sum.inr X) : OspBasis F n)
        * rhoBasis (Sum.inr (Sum.inr X) : OspBasis F n) (Sum.inr (v0.1, !v0.2))
          (Sum.inr u0) = 0 := by
    intro ⟨w, i⟩
    change c _ * (rhoBasis (Sum.inr (Sum.inr (w, i)) : OspBasis F n)
        (Sum.inr (v0.1, !v0.2)) : MMod F n) (Sum.inr u0) = 0
    simp [rhoBasis, eNM]
  rw [Finset.sum_congr rfl (fun X _ => hS X), Finset.sum_congr rfl (fun X _ => hFp X)] at h1
  simp only [Finset.sum_const_zero, add_zero] at h1
  rw [Finset.sum_eq_single (⟨(u0, v0), huv0⟩ : {p : I n × I n // IKey p.1 ≤ IKey p.2})] at h1
  · simp only [rhoBasis, Pi.smul_apply, Pi.add_apply, smul_eq_mul, eNM_I_eq, ite_true] at h1
    obtain ⟨k0, b0⟩ := v0
    rw [show (1 / 2 : ℚ) * ((J n (k0, b0) ((k0, b0).1, !(k0, b0).2) * 1) +
          J n u0 ((k0, b0).1, !(k0, b0).2) * if u0 = (k0, b0) then 1 else 0)
        = (1 / 2 : ℚ) * ((J n ((k0, b0) : I n) (k0, !b0) * if u0 = u0 then (1 : ℚ) else 0)
          + J n u0 (k0, !b0) * if u0 = (k0, b0) then (1 : ℚ) else 0) from by simp] at h1
    rcases mul_eq_zero.mp h1 with h1 | h1
    · exact h1
    · exfalso
      apply J_diag_ne_zero n k0 b0 u0
      rcases mul_eq_zero.mp h1 with h1 | h1
      · norm_num at h1
      · exact h1
  · intro X _ hne
    obtain ⟨⟨u', v'⟩, huv'⟩ := X
    change c (Sum.inl ⟨(u', v'), huv'⟩ : OspBasis F n)
        * (rhoBasis (Sum.inl ⟨(u', v'), huv'⟩ : OspBasis F n)
            (Sum.inr (v0.1, !v0.2)) : MMod F n) (Sum.inr u0) = 0
    simp only [rhoBasis, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    exact mul_eq_zero_of_right _ (L_indep_other F n u0 v0 u' v' huv0 huv' hne)
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## `rhoBasis_linearIndependent`'s own toolkit -- `S`-kind coefficient extraction

Mirrors `L_indep_full`'s route but simpler: `S`-kind's own basis type requires the
*strict* order `F.key i < F.key j`, so there is no `u0=v0`-style diagonal case, and no
`IKey_injective`-style "reversed pair" exclusion is needed. Evaluate at input `inl
(F.dual j0)`, read the `inl i0`-component; `g_dual_right` (`F.g a (F.dual b) = 1` iff
`a=b`, else `0`, the `F.K` analogue of `J`'s single-match property) picks out the target
pair directly. -/

theorem g_dual_right {F : FermionIndex} (a b : F.K) :
    F.g a (F.dual b) = if a = b then (1 : ℚ) else 0 := by
  unfold FermionIndex.g
  by_cases h : a = b
  · subst h; simp
  · have hne : F.dual a ≠ F.dual b := fun hc => h (by
      have := congrArg F.dual hc; rwa [F.dual_dual, F.dual_dual] at this)
    simp [h, Ne.symm hne]

theorem eNM_K_eq {F : FermionIndex} {n : ℕ} (Z k : F.K) :
    (eNM (Sum.inl Z) : MMod F n) (Sum.inl k) = if k = Z then (1 : ℚ) else 0 := by
  unfold eNM
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (Sum.inl.inj_iff.mp h1) h2
  · exact absurd (by rw [h2]) h1
  · rfl

/-- Every `S`-kind pair OTHER than the target `(i0,j0)` contributes `0` to the `(inl
i0)`-component of `bracketSS`'s own `rhoBasis` value, evaluated at `inl (F.dual j0)`:
one product term is excluded by the pair not matching `(i0,j0)` (mirrors `L_indep_other`,
no `IKey_injective` needed since `S`-kind has no diagonal), the other purely by the
strict-order impossibility `F.key j0 < F.key i0` it would force via `hij0.trans hij'`. -/
theorem S_indep_other (F : FermionIndex) (n : ℕ) (i0 j0 i' j' : F.K)
    (hij0 : F.key i0 < F.key j0) (hij' : F.key i' < F.key j')
    (hne : (⟨(i', j'), hij'⟩ : {p : F.K × F.K // F.key p.1 < F.key p.2})
        ≠ ⟨(i0, j0), hij0⟩) :
    (F.g j' (F.dual j0) * ((eNM (Sum.inl i') : MMod F n) (Sum.inl i0))
      - F.g i' (F.dual j0) * ((eNM (Sum.inl j') : MMod F n) (Sum.inl i0))) = 0 := by
  rw [eNM_K_eq, eNM_K_eq, g_dual_right, g_dual_right]
  have hpne : (i', j') ≠ (i0, j0) := fun h => hne (by rw [Subtype.mk.injEq]; exact h)
  have hterm1 : (if j' = j0 then (1 : ℚ) else 0) * (if i0 = i' then (1 : ℚ) else 0) = 0 := by
    by_cases h1 : j' = j0
    · by_cases h2 : i0 = i'
      · exact absurd (Prod.ext h2.symm h1) hpne
      · simp [h2]
    · simp [h1]
  have hterm2 : (if i' = j0 then (1 : ℚ) else 0) * (if i0 = j' then (1 : ℚ) else 0) = 0 := by
    by_cases h3 : i' = j0
    · by_cases h4 : i0 = j'
      · exfalso
        rw [h3] at hij'
        rw [← h4] at hij'
        exact absurd (hij0.trans hij') (lt_irrefl _)
      · simp [h4]
    · simp [h3]
  rw [hterm1, hterm2]
  ring

/-- **The `S`-kind case of `rhoBasis_linearIndependent`**, mirroring `L_indep_full`. -/
theorem S_indep_full (F : FermionIndex) (n : ℕ) (c : OspBasis F n → ℚ)
    (hc : ∑ X : OspBasis F n, c X • rhoBasis X = 0)
    (i0 j0 : F.K) (hij0 : F.key i0 < F.key j0) :
    c (Sum.inr (Sum.inl ⟨(i0, j0), hij0⟩) : OspBasis F n) = 0 := by
  have h1 := congrFun (congrFun hc (Sum.inl (F.dual j0))) (Sum.inl i0)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
  rw [show (0 : Midx F n → MMod F n) (Sum.inl (F.dual j0)) (Sum.inl i0) = (0 : ℚ) from rfl] at h1
  have hsplit1 : (∑ X : OspBasis F n, c X * rhoBasis X (Sum.inl (F.dual j0)) (Sum.inl i0))
      = ∑ a : {p : I n × I n // IKey p.1 ≤ IKey p.2},
          c (Sum.inl a) * rhoBasis (Sum.inl a) (Sum.inl (F.dual j0)) (Sum.inl i0)
        + ∑ b : ({p : F.K × F.K // F.key p.1 < F.key p.2} ⊕ (I n × F.K)),
          c (Sum.inr b) * rhoBasis (Sum.inr b) (Sum.inl (F.dual j0)) (Sum.inl i0) :=
    Fintype.sum_sum_type (fun X => c X * rhoBasis X (Sum.inl (F.dual j0)) (Sum.inl i0))
  rw [hsplit1] at h1
  have hsplit2 : (∑ b : ({p : F.K × F.K // F.key p.1 < F.key p.2} ⊕ (I n × F.K)),
        c (Sum.inr b) * rhoBasis (Sum.inr b : OspBasis F n) (Sum.inl (F.dual j0)) (Sum.inl i0))
      = ∑ Y : {p : F.K × F.K // F.key p.1 < F.key p.2},
          c (Sum.inr (Sum.inl Y))
            * rhoBasis (Sum.inr (Sum.inl Y) : OspBasis F n) (Sum.inl (F.dual j0)) (Sum.inl i0)
        + ∑ Z : I n × F.K,
          c (Sum.inr (Sum.inr Z))
            * rhoBasis (Sum.inr (Sum.inr Z) : OspBasis F n) (Sum.inl (F.dual j0)) (Sum.inl i0) :=
    Fintype.sum_sum_type (fun b =>
      c (Sum.inr b) * rhoBasis (Sum.inr b : OspBasis F n) (Sum.inl (F.dual j0)) (Sum.inl i0))
  rw [hsplit2] at h1
  have hL : ∀ X : {p : I n × I n // IKey p.1 ≤ IKey p.2},
      c (Sum.inl X : OspBasis F n)
        * rhoBasis (Sum.inl X : OspBasis F n) (Sum.inl (F.dual j0)) (Sum.inl i0) = 0 := by
    intro X
    obtain ⟨⟨u, v⟩, huv⟩ := X
    show c _ * (rhoBasis (Sum.inl ⟨(u,v),huv⟩ : OspBasis F n)
        (Sum.inl (F.dual j0)) : MMod F n) (Sum.inl i0) = 0
    simp only [rhoBasis]
    rw [show (0 : MMod F n) (Sum.inl i0) = (0 : ℚ) from rfl, mul_zero]
  have hFp : ∀ X : I n × F.K,
      c (Sum.inr (Sum.inr X) : OspBasis F n)
        * rhoBasis (Sum.inr (Sum.inr X) : OspBasis F n) (Sum.inl (F.dual j0)) (Sum.inl i0) = 0 := by
    intro ⟨w, i⟩
    change c _ * (rhoBasis (Sum.inr (Sum.inr (w,i)) : OspBasis F n)
        (Sum.inl (F.dual j0)) : MMod F n) (Sum.inl i0) = 0
    simp [rhoBasis, eNM]
  rw [Finset.sum_congr rfl (fun X _ => hL X), Finset.sum_congr rfl (fun X _ => hFp X)] at h1
  simp only [Finset.sum_const_zero, zero_add] at h1
  rw [Finset.sum_eq_single (⟨(i0,j0), hij0⟩ : {p : F.K × F.K // F.key p.1 < F.key p.2})] at h1
  · simp only [rhoBasis, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, eNM_K_eq, g_dual_right] at h1
    have hi0j0 : i0 ≠ j0 := fun h => absurd hij0 (h ▸ lt_irrefl _)
    simp only [↓reduceIte, mul_one, hi0j0, mul_zero, sub_zero, add_zero] at h1
    exact h1
  · intro X _ hne
    obtain ⟨⟨i', j'⟩, hij'⟩ := X
    change c (Sum.inr (Sum.inl ⟨(i',j'),hij'⟩) : OspBasis F n)
        * (rhoBasis (Sum.inr (Sum.inl ⟨(i',j'),hij'⟩) : OspBasis F n)
            (Sum.inl (F.dual j0)) : MMod F n) (Sum.inl i0) = 0
    simp only [rhoBasis, Pi.sub_apply]
    exact mul_eq_zero_of_right _ (S_indep_other F n i0 j0 i' j' hij0 hij' hne)
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## `rhoBasis_linearIndependent`'s own toolkit -- `F`-kind coefficient extraction

Simplest of the three: no ordering constraint at all (`F`-kind's own basis type is the
plain product `I n × F.K`), so the "other pairs vanish" argument needs only direct
equality case-splits, no order-theoretic impossibility. Evaluate at input `inl (F.dual
i0)`, read the `inr u0`-component: `L`- and `S`-kind both vanish there (`L`-kind's own
`rhoBasis` sends every `inl`-kind input to `0` outright; `S`-kind's own output is
`inl`-supported only, missing the `inr u0` component read here), and `g_dual_right`
picks out the target pair among the `F`-kind ones exactly as in the `S`-kind case. -/

theorem eNM_inl_inr_eq_zero {F : FermionIndex} {n : ℕ} (i : F.K) (u : I n) :
    (eNM (Sum.inl i) : MMod F n) (Sum.inr u) = 0 := by
  unfold eNM
  simp

theorem F_indep_other (F : FermionIndex) (n : ℕ) (u0 : I n) (i0 : F.K) (u' : I n) (i' : F.K)
    (hne : (u', i') ≠ (u0, i0)) :
    (1 / 2 : ℚ) * (F.g i' (F.dual i0) * ((eNM (Sum.inr u') : MMod F n) (Sum.inr u0))) = 0 := by
  rw [eNM_I_eq, g_dual_right]
  by_cases hu : u0 = u'
  · by_cases hi : i' = i0
    · exact absurd (by rw [← hu, hi]) hne
    · simp [hi]
  · simp [hu]

/-- **The `F`-kind case of `rhoBasis_linearIndependent`**, mirroring `S_indep_full`. -/
theorem F_indep_full (F : FermionIndex) (n : ℕ) (c : OspBasis F n → ℚ)
    (hc : ∑ X : OspBasis F n, c X • rhoBasis X = 0)
    (u0 : I n) (i0 : F.K) :
    c (Sum.inr (Sum.inr (u0, i0)) : OspBasis F n) = 0 := by
  have h1 := congrFun (congrFun hc (Sum.inl (F.dual i0))) (Sum.inr u0)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
  rw [show (0 : Midx F n → MMod F n) (Sum.inl (F.dual i0)) (Sum.inr u0) = (0 : ℚ) from rfl] at h1
  have hsplit1 : (∑ X : OspBasis F n, c X * rhoBasis X (Sum.inl (F.dual i0)) (Sum.inr u0))
      = ∑ a : {p : I n × I n // IKey p.1 ≤ IKey p.2},
          c (Sum.inl a) * rhoBasis (Sum.inl a) (Sum.inl (F.dual i0)) (Sum.inr u0)
        + ∑ b : ({p : F.K × F.K // F.key p.1 < F.key p.2} ⊕ (I n × F.K)),
          c (Sum.inr b) * rhoBasis (Sum.inr b) (Sum.inl (F.dual i0)) (Sum.inr u0) :=
    Fintype.sum_sum_type (fun X => c X * rhoBasis X (Sum.inl (F.dual i0)) (Sum.inr u0))
  rw [hsplit1] at h1
  have hsplit2 : (∑ b : ({p : F.K × F.K // F.key p.1 < F.key p.2} ⊕ (I n × F.K)),
        c (Sum.inr b) * rhoBasis (Sum.inr b : OspBasis F n) (Sum.inl (F.dual i0)) (Sum.inr u0))
      = ∑ Y : {p : F.K × F.K // F.key p.1 < F.key p.2},
          c (Sum.inr (Sum.inl Y))
            * rhoBasis (Sum.inr (Sum.inl Y) : OspBasis F n) (Sum.inl (F.dual i0)) (Sum.inr u0)
        + ∑ Z : I n × F.K,
          c (Sum.inr (Sum.inr Z))
            * rhoBasis (Sum.inr (Sum.inr Z) : OspBasis F n) (Sum.inl (F.dual i0)) (Sum.inr u0) :=
    Fintype.sum_sum_type (fun b =>
      c (Sum.inr b) * rhoBasis (Sum.inr b : OspBasis F n) (Sum.inl (F.dual i0)) (Sum.inr u0))
  rw [hsplit2] at h1
  have hL : ∀ X : {p : I n × I n // IKey p.1 ≤ IKey p.2},
      c (Sum.inl X : OspBasis F n)
        * rhoBasis (Sum.inl X : OspBasis F n) (Sum.inl (F.dual i0)) (Sum.inr u0) = 0 := by
    intro X
    obtain ⟨⟨u, v⟩, huv⟩ := X
    show c _ * (rhoBasis (Sum.inl ⟨(u,v),huv⟩ : OspBasis F n)
        (Sum.inl (F.dual i0)) : MMod F n) (Sum.inr u0) = 0
    simp only [rhoBasis]
    rw [show (0 : MMod F n) (Sum.inr u0) = (0 : ℚ) from rfl, mul_zero]
  have hS : ∀ X : {p : F.K × F.K // F.key p.1 < F.key p.2},
      c (Sum.inr (Sum.inl X) : OspBasis F n)
        * rhoBasis (Sum.inr (Sum.inl X) : OspBasis F n) (Sum.inl (F.dual i0)) (Sum.inr u0) = 0 := by
    intro X
    obtain ⟨⟨i, j⟩, hij⟩ := X
    show c _ * (rhoBasis (Sum.inr (Sum.inl ⟨(i,j),hij⟩) : OspBasis F n)
        (Sum.inl (F.dual i0)) : MMod F n) (Sum.inr u0) = 0
    simp [rhoBasis, Pi.sub_apply, Pi.smul_apply, eNM_inl_inr_eq_zero]
  rw [Finset.sum_congr rfl (fun X _ => hL X), Finset.sum_congr rfl (fun X _ => hS X)] at h1
  simp only [Finset.sum_const_zero, zero_add] at h1
  rw [Finset.sum_eq_single ((u0, i0) : I n × F.K)] at h1
  · simp only [rhoBasis, Pi.smul_apply, smul_eq_mul, eNM_I_eq, ite_true, g_dual_right] at h1
    simpa using h1
  · intro X _ hne
    obtain ⟨u', i'⟩ := X
    change c (Sum.inr (Sum.inr (u', i')) : OspBasis F n)
        * (rhoBasis (Sum.inr (Sum.inr (u', i')) : OspBasis F n)
            (Sum.inl (F.dual i0)) : MMod F n) (Sum.inr u0) = 0
    simp only [rhoBasis, Pi.smul_apply, smul_eq_mul]
    exact mul_eq_zero_of_right _ (F_indep_other F n u0 i0 u' i' hne)
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Injectivity half of bijectivity** (paper Prop. 3.4, part "Bijectivity"):
the family `{rhoBasis X}` is linearly independent in `Midx F n → MMod F n`. Assembled
from the three kind-cases above (`L_indep_full`, `S_indep_full`, `F_indep_full`) via
`Fintype.linearIndependent_iff`, matching `OspBasis F n`'s own three-way `Sum` shape. -/
theorem rhoBasis_linearIndependent (F : FermionIndex) (n : ℕ) :
    LinearIndependent ℚ (fun X : OspBasis F n => rhoBasis X) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc X
  match X with
  | .inl ⟨(u, v), h⟩ => exact L_indep_full F n c hc u v h
  | .inr (.inl ⟨(i, j), h⟩) => exact S_indep_full F n c hc i j h
  | .inr (.inr (u, i)) => exact F_indep_full F n c hc u i

/-- `Tb` is homogeneous of parity `p` when it maps `M_q`
into `M_{q+p}` — i.e. every nonzero entry `Tb i j` forces `j`'s own `M`-parity to be `i`'s
own plus `p`. Needed to state `rho_span` (surjectivity), since `rhoBasis_linearIndependent`
alone gives only an injective homomorphism, not the isomorphism of Prop. 3.4. -/
def Homogeneous {F : FermionIndex} {n : ℕ} (p : ZMod 2) (Tb : Midx F n → MMod F n) : Prop :=
  ∀ i j : Midx F n, Tb i j ≠ 0 → pM j = pM i + p

/-! ## `rho_span`'s own toolkit -- general-purpose pieces, reusable for every parity

`rhoBasis_homogeneous` (each `rhoBasis X` is itself homogeneous of parity `parity X`)
and `rhoCombo_ospCond`/`rhoCombo_homogeneous` (a `c`-supported combination of `rhoBasis`
inherits both `ospCond p` and `Homogeneous p` from `rho_ospCond`/`rhoBasis_homogeneous`,
by bilinearity/case-split on which `X`'s survive `c`'s own support condition) are used
for EVERY parity `p`, not just the odd case below. `Homogeneous_sub`/`ospCond_sub` (both
properties are preserved under subtracting two same-parity maps) let the argument work
with `D := Tb - candSum` directly. `Bpair_sum_left`/`_right` (`Bpair`'s bilinearity,
extended from two terms to a finite sum by induction) and `Bpair_eNM_inl` (`𝓑(x,e_k)`
collapses to `-Σ_a x(a)•g_{a,k}`, the F.K-block analogue of `Bpair_eNM_eNM`) are the
computational core. -/

theorem eNM_inr_inl_eq_zero {F : FermionIndex} {n : ℕ} (u : I n) (i : F.K) :
    (eNM (Sum.inr u) : MMod F n) (Sum.inl i) = 0 := by unfold eNM; simp

/-- Every `rhoBasis X` is homogeneous of its own parity: case-split on `X`'s kind then
`i,j`'s `Midx`-kind (as `rho_ospCond` did), most cases closing from the outer `match`'s
own structure or `eNM`'s support, the "correct parity" cases closing by `decide` on
`ZMod 2`. -/
theorem rhoBasis_homogeneous {F : FermionIndex} {n : ℕ} (X : OspBasis F n) :
    Homogeneous (parity X) (rhoBasis X) := by
  intro i j hij
  match X with
  | .inl ⟨(u, v), huv⟩ =>
    rcases i with k1 | w <;> rcases j with k2 | w2 <;>
      simp only [rhoBasis, parity, pM] at *
    · exact absurd rfl hij
    · exact absurd rfl hij
    · simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, eNM_inr_inl_eq_zero] at hij; simp_all
    · decide
  | .inr (.inl ⟨(i0, j0), hij0⟩) =>
    rcases i with k1 | w <;> rcases j with k2 | w2 <;>
      simp only [rhoBasis, parity, pM] at *
    · decide
    · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, eNM_inl_inr_eq_zero] at hij; simp_all
    · exact absurd rfl hij
    · exact absurd rfl hij
  | .inr (.inr (u, i0)) =>
    rcases i with k1 | w <;> rcases j with k2 | w2 <;>
      simp only [rhoBasis, parity, pM] at *
    · simp only [Pi.smul_apply, smul_eq_mul, eNM_inr_inl_eq_zero] at hij; simp_all
    · decide
    · decide
    · simp only [Pi.smul_apply, smul_eq_mul, eNM_inl_inr_eq_zero] at hij; simp_all

theorem Bpair_sum_left {F : FermionIndex} {n : ℕ} {ι : Type*} (s : Finset ι)
    (x : ι → MMod F n) (y : MMod F n) :
    Bpair (∑ i ∈ s, x i) y = ∑ i ∈ s, Bpair (x i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Bpair_zero_left]
  | insert a s' ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Bpair_add_left, ih]

theorem Bpair_sum_right {F : FermionIndex} {n : ℕ} {ι : Type*} (s : Finset ι)
    (x : MMod F n) (y : ι → MMod F n) :
    Bpair x (∑ i ∈ s, y i) = ∑ i ∈ s, Bpair x (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Bpair_zero_right]
  | insert a s' ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Bpair_add_right, ih]

/-- A `c`-supported combination of `rhoBasis` satisfies `ospCond p`: expand `Bpair`
over the finite sum via `Bpair_sum_left`/`_right`, then for each `X` either `c X = 0`
(the term vanishes outright) or `parity X = p` (forced by `hc`'s contrapositive), letting
`rho_ospCond X` close that term to `0` directly. -/
theorem rhoCombo_ospCond {F : FermionIndex} {n : ℕ} (p : ZMod 2) (c : OspBasis F n → ℚ)
    (hc : ∀ X, parity X ≠ p → c X = 0) :
    ospCond p (fun i => ∑ X : OspBasis F n, c X • rhoBasis X i) := by
  intro i j
  have hl : Bpair (∑ X : OspBasis F n, c X • rhoBasis X i) (eNM j)
      = ∑ X : OspBasis F n, c X * Bpair (rhoBasis X i) (eNM j) := by
    rw [Bpair_sum_left]; apply Finset.sum_congr rfl; intro X _; rw [Bpair_smul_left]
  have hr : Bpair (eNM i) (∑ X : OspBasis F n, c X • rhoBasis X j)
      = ∑ X : OspBasis F n, c X * Bpair (eNM i) (rhoBasis X j) := by
    rw [Bpair_sum_right]; apply Finset.sum_congr rfl; intro X _; rw [Bpair_smul_right]
  rw [hl, hr, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro X _
  by_cases hX : c X = 0
  · simp [hX]
  · have hp : parity X = p := by by_contra hne; exact hX (hc X hne)
    have h := rho_ospCond X i j
    rw [hp, smul_eq_mul] at h
    have h2 := congrArg (fun x => c X * x) h
    simp only [mul_add, mul_zero] at h2
    linarith [h2, mul_left_comm (gsign p (pM i)) (c X) (Bpair (eNM i) (rhoBasis X j)),
      mul_left_comm (c X) (gsign p (pM i)) (Bpair (eNM i) (rhoBasis X j))]

/-- A `c`-supported combination of `rhoBasis` is `Homogeneous p`: contrapositive, using
`rhoBasis_homogeneous` termwise exactly as `rhoCombo_ospCond` uses `rho_ospCond`. -/
theorem rhoCombo_homogeneous {F : FermionIndex} {n : ℕ} (p : ZMod 2) (c : OspBasis F n → ℚ)
    (hc : ∀ X, parity X ≠ p → c X = 0) :
    Homogeneous p (fun i => ∑ X : OspBasis F n, c X • rhoBasis X i) := by
  intro i j hne
  by_contra hc2
  apply hne
  change (∑ X : OspBasis F n, c X • rhoBasis X i) j = 0
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro X _
  by_cases hX : c X = 0
  · simp [hX]
  · have hp : parity X = p := by by_contra hne'; exact hX (hc X hne')
    have hzero : rhoBasis X i j = 0 := by
      by_contra hz; exact hc2 (hp ▸ rhoBasis_homogeneous X i j hz)
    simp [hzero]

theorem Homogeneous_sub {F : FermionIndex} {n : ℕ} (p : ZMod 2) (Tb1 Tb2 : Midx F n → MMod F n)
    (h1 : Homogeneous p Tb1) (h2 : Homogeneous p Tb2) : Homogeneous p (Tb1 - Tb2) := by
  intro i j hne
  by_contra hc
  apply hne
  have e1 : Tb1 i j = 0 := by by_contra hz; exact hc (h1 i j hz)
  have e2 : Tb2 i j = 0 := by by_contra hz; exact hc (h2 i j hz)
  change (Tb1 - Tb2) i j = 0
  simp [Pi.sub_apply, e1, e2]

theorem ospCond_sub {F : FermionIndex} {n : ℕ} (p : ZMod 2) (Tb1 Tb2 : Midx F n → MMod F n)
    (h1 : ospCond p Tb1) (h2 : ospCond p Tb2) : ospCond p (Tb1 - Tb2) := by
  intro i j
  have e1 := h1 i j
  have e2 := h2 i j
  change Bpair ((Tb1 - Tb2) i) (eNM j) + gsign p (pM i) • Bpair (eNM i) ((Tb1 - Tb2) j) = 0
  simp only [Pi.sub_apply]
  rw [Bpair_sub_left, Bpair_sub_right, smul_sub]
  have : Bpair (Tb1 i) (eNM j) + gsign p (pM i) • Bpair (eNM i) (Tb1 j)
      - (Bpair (Tb2 i) (eNM j) + gsign p (pM i) • Bpair (eNM i) (Tb2 j)) = 0 := by
    rw [e1, e2]; ring
  linarith [this]

/-- `𝓑(x,e_k) = -Σ_a x(a)•g_{a,k}` for `k:F.K` -- the `F.K`-block collapse of `Bpair`
against a single basis vector (the general analogue of `Bpair_eNM_eNM`'s own value at a
basis PAIR): the inner sum over `eNM (Sum.inl k)` picks its one diagonal term, the outer
sum over `Midx F n` splits and its `I n`-part vanishes (`Bform`'s mixed values are `0`).
Needed for `rho_span_odd`'s own second step (recovering `D`'s `inr`-block from its
already-known-zero `inl`-block via `ospCond`). -/
theorem Bpair_eNM_inl {F : FermionIndex} {n : ℕ} (x : MMod F n) (k : F.K) :
    Bpair x (eNM (Sum.inl k)) = -∑ a : F.K, x (Sum.inl a) * F.g a k := by
  unfold Bpair
  have step1 : (∑ i : Midx F n, ∑ j : Midx F n, x i * (eNM (Sum.inl k : Midx F n)) j * Bform i j)
      = ∑ i : Midx F n, x i * Bform i (Sum.inl k) := by
    apply Finset.sum_congr rfl
    intro i _
    have hone : (eNM (Sum.inl k : Midx F n) : MMod F n) (Sum.inl k) = 1 := by unfold eNM; simp
    have hcollapse : (∑ j : Midx F n, x i * (eNM (Sum.inl k : Midx F n)) j * Bform i j)
        = x i * (eNM (Sum.inl k : Midx F n)) (Sum.inl k) * Bform i (Sum.inl k) := by
      apply Finset.sum_eq_single (Sum.inl k : Midx F n)
      · intro b _ hb
        have hz : (eNM (Sum.inl k : Midx F n) : MMod F n) b = 0 := by
          unfold eNM; split_ifs with h
          · exact absurd h hb
          · rfl
        rw [hz, mul_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hcollapse, hone, mul_one]
  rw [step1]
  have step2 : (∑ i : Midx F n, x i * Bform i (Sum.inl k))
      = ∑ a : F.K, x (Sum.inl a) * Bform (Sum.inl a) (Sum.inl k)
        + ∑ b : I n, x (Sum.inr b) * Bform (Sum.inr b) (Sum.inl k) :=
    Fintype.sum_sum_type (fun i => x i * Bform i (Sum.inl k))
  rw [step2]
  have hz : ∑ b : I n, x (Sum.inr b) * Bform (Sum.inr b) (Sum.inl k) = 0 := by
    apply Finset.sum_eq_zero; intro b _; unfold Bform; simp
  rw [hz, add_zero]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  unfold Bform; ring

/-! ## `rho_span`'s odd case (`p = 1`)

The even case (`p = 0`, the `L`/`S`-kind coefficients), treated in the sections below, is
structurally different from (and heavier than) this odd case.

The odd case exploits the paper's own remark that an odd `T` is *determined by its
restriction to `M_0̄`* (the `F.K`-indexed part): `cOdd Tb`'s only nonzero values are on
`F`-kind pairs, read directly off `Tb`'s own `inl`-block via `F.dual`'s involution and
`g_dual_right` (`cOdd_inl_inr`, mirroring `F_indep_full`'s own extraction but matching
`Tb`'s FULL row at every column, not just one diagnostic point -- no use of `ospCond` on
`Tb` itself is needed for this step, `Tb`'s `inl`-block is matched purely by direct sum
inversion). This already forces `D := Tb - candSum` to vanish entirely on `D`'s own
`inl`-block (`cOdd_inl_inl`+`cOdd_inl_inr` cover both sub-cases of `D(inl k) = 0`). The
SECOND step recovers `D`'s `inr`-block from this: `ospCond 1 D` at `(inr u, inl k')`,
with `D(inl _) = 0` already known, forces `Bpair(D(inr u), eNM(inl k')) = 0` for every
`k'`, and `Bpair_eNM_inl` + `g_dual_right` (evaluated at `k' ↦ F.dual k'` to pick out
exactly the `k'`-component) then forces `D(inr u)(inl k') = 0` too -- closing `D = 0`
entirely, since `Homogeneous 1 D` rules out `D`'s remaining (`inr`,`inr`) block
automatically (wrong parity). -/

def cOdd {F : FermionIndex} {n : ℕ} (Tb : Midx F n → MMod F n) : OspBasis F n → ℚ
  | .inl _ => 0
  | .inr (.inl _) => 0
  | .inr (.inr (u, i)) => 2 * Tb (Sum.inl (F.dual i)) (Sum.inr u)

theorem cOdd_support {F : FermionIndex} {n : ℕ} (Tb : Midx F n → MMod F n) :
    ∀ X : OspBasis F n, parity X ≠ 1 → cOdd Tb X = 0 := by
  intro X hX
  match X with
  | .inl _ => rfl
  | .inr (.inl _) => rfl
  | .inr (.inr _) => exact absurd rfl hX

/-- `candSum`'s own `inl k` row matches `Tb`'s at every `inr u0` column: the sum over
`F`-kind pairs collapses (as in `F_indep_full`) but now over the WHOLE row, not one
diagnostic point, via the same `F.dual`-reindexing + `g_dual_right` + `F.g_symm`
argument used there. -/
theorem cOdd_inl_inr {F : FermionIndex} {n : ℕ} (Tb : Midx F n → MMod F n) (k : F.K) (u0 : I n) :
    (∑ X : OspBasis F n, cOdd Tb X • rhoBasis X (Sum.inl k)) (Sum.inr u0)
      = Tb (Sum.inl k) (Sum.inr u0) := by
  have goal2 : (∑ X : OspBasis F n, cOdd Tb X • rhoBasis X (Sum.inl k)) (Sum.inr u0)
      = ∑ X : OspBasis F n, cOdd Tb X * rhoBasis X (Sum.inl k) (Sum.inr u0) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [goal2]
  have hsplit1 : (∑ X : OspBasis F n, cOdd Tb X * rhoBasis X (Sum.inl k) (Sum.inr u0))
      = ∑ a : {p : I n × I n // IKey p.1 ≤ IKey p.2},
          cOdd Tb (Sum.inl a) * rhoBasis (Sum.inl a : OspBasis F n) (Sum.inl k) (Sum.inr u0)
        + ∑ b : ({p : F.K × F.K // F.key p.1 < F.key p.2} ⊕ (I n × F.K)),
          cOdd Tb (Sum.inr b) * rhoBasis (Sum.inr b : OspBasis F n) (Sum.inl k) (Sum.inr u0) :=
    Fintype.sum_sum_type (fun X => cOdd Tb X * rhoBasis X (Sum.inl k) (Sum.inr u0))
  rw [hsplit1]
  have hsplit2 : (∑ b : ({p : F.K × F.K // F.key p.1 < F.key p.2} ⊕ (I n × F.K)),
        cOdd Tb (Sum.inr b) * rhoBasis (Sum.inr b : OspBasis F n) (Sum.inl k) (Sum.inr u0))
      = ∑ Y : {p : F.K × F.K // F.key p.1 < F.key p.2},
          cOdd Tb (Sum.inr (Sum.inl Y)) * rhoBasis (Sum.inr (Sum.inl Y) : OspBasis F n)
            (Sum.inl k) (Sum.inr u0)
        + ∑ Z : I n × F.K,
          cOdd Tb (Sum.inr (Sum.inr Z)) * rhoBasis (Sum.inr (Sum.inr Z) : OspBasis F n)
            (Sum.inl k) (Sum.inr u0) :=
    Fintype.sum_sum_type
      (fun b => cOdd Tb (Sum.inr b) * rhoBasis (Sum.inr b : OspBasis F n) (Sum.inl k) (Sum.inr u0))
  rw [hsplit2]
  have hL : ∑ a : {p : I n × I n // IKey p.1 ≤ IKey p.2},
      cOdd Tb (Sum.inl a) * rhoBasis (Sum.inl a : OspBasis F n) (Sum.inl k) (Sum.inr u0) = 0 := by
    apply Finset.sum_eq_zero; intro X _; obtain ⟨⟨u,v⟩,huv⟩ := X; simp [cOdd]
  have hS : ∑ Y : {p : F.K × F.K // F.key p.1 < F.key p.2},
      cOdd Tb (Sum.inr (Sum.inl Y)) * rhoBasis (Sum.inr (Sum.inl Y) : OspBasis F n)
        (Sum.inl k) (Sum.inr u0) = 0 := by
    apply Finset.sum_eq_zero; intro X _; obtain ⟨⟨i,j⟩,hij⟩ := X; simp [cOdd]
  rw [hL, hS, zero_add, zero_add]
  have hF : (∑ Z : I n × F.K,
      cOdd Tb (Sum.inr (Sum.inr Z)) * rhoBasis (Sum.inr (Sum.inr Z) : OspBasis F n)
        (Sum.inl k) (Sum.inr u0))
      = ∑ u : I n, ∑ i : F.K,
          cOdd Tb (Sum.inr (Sum.inr (u,i))) * rhoBasis (Sum.inr (Sum.inr (u,i)) : OspBasis F n)
            (Sum.inl k) (Sum.inr u0) :=
    Fintype.sum_prod_type _
  rw [hF]
  rw [Finset.sum_eq_single u0]
  · rw [show (∑ i : F.K, cOdd Tb (Sum.inr (Sum.inr (u0,i)))
        * rhoBasis (Sum.inr (Sum.inr (u0,i)) : OspBasis F n) (Sum.inl k) (Sum.inr u0))
        = ∑ i : F.K, Tb (Sum.inl (F.dual i)) (Sum.inr u0) * F.g i k from by
      apply Finset.sum_congr rfl; intro i _
      change cOdd Tb (Sum.inr (Sum.inr (u0,i))) *
          ((1/2:ℚ) • (F.g i k • eNM (Sum.inr u0) : MMod F n)) (Sum.inr u0) = _
      simp only [cOdd, Pi.smul_apply, smul_eq_mul, eNM_I_eq]
      simp; ring]
    have hreindex : (∑ i : F.K, Tb (Sum.inl (F.dual i)) (Sum.inr u0) * F.g i k)
        = ∑ i : F.K, Tb (Sum.inl i) (Sum.inr u0) * F.g (F.dual i) k := by
      apply Fintype.sum_bijective F.dual
      · exact Function.Involutive.bijective F.dual_dual
      · intro i; rw [F.dual_dual]
    rw [hreindex, Finset.sum_eq_single k]
    · rw [F.g_symm, g_dual_right]; simp
    · intro b _ hb
      rw [F.g_symm, g_dual_right]; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro u _ hu
    apply Finset.sum_eq_zero; intro i _
    change cOdd Tb (Sum.inr (Sum.inr (u,i))) *
        ((1/2:ℚ) • (F.g i k • eNM (Sum.inr u) : MMod F n)) (Sum.inr u0) = 0
    simp only [Pi.smul_apply, smul_eq_mul, eNM_I_eq]
    rw [ite_eq_right (Ne.symm hu)]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `candSum`'s own `inl k` row matches `Tb`'s at every `inl k'` column too, both sides
`0`: `Tb(inl k)(inl k') = 0` from `Homogeneous 1 Tb` (wrong parity), `candSum`'s value
`0` since `F`-kind's own `inl`-branch is `eNM (inr _)`-valued, vanishing at `inl k'`. -/
theorem cOdd_inl_inl {F : FermionIndex} {n : ℕ} (Tb : Midx F n → MMod F n)
    (hh : Homogeneous 1 Tb) (k k' : F.K) :
    (∑ X : OspBasis F n, cOdd Tb X • rhoBasis X (Sum.inl k)) (Sum.inl k')
      = Tb (Sum.inl k) (Sum.inl k') := by
  have hTb : Tb (Sum.inl k) (Sum.inl k') = 0 := by
    by_contra hz
    have := hh (Sum.inl k) (Sum.inl k') hz
    simp only [pM] at this
    exact absurd this (by decide)
  rw [hTb]
  have goal2 : (∑ X : OspBasis F n, cOdd Tb X • rhoBasis X (Sum.inl k)) (Sum.inl k')
      = ∑ X : OspBasis F n, cOdd Tb X * rhoBasis X (Sum.inl k) (Sum.inl k') := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [goal2]
  apply Finset.sum_eq_zero
  intro X _
  match X with
  | .inl ⟨(u,v),huv⟩ => simp [cOdd]
  | .inr (.inl ⟨(i,j),hij⟩) => simp [cOdd]
  | .inr (.inr (u,i)) =>
    change cOdd Tb (Sum.inr (Sum.inr (u,i))) *
        ((1/2:ℚ) • (F.g i k • eNM (Sum.inr u) : MMod F n)) (Sum.inl k') = 0
    have : (eNM (Sum.inr u) : MMod F n) (Sum.inl k') = 0 := by unfold eNM; simp
    simp [this]

/-- **`rho_span`, restricted to `p = 1` (odd `Tb`)** -- the surjectivity half of
Prop. 3.4's "Bijectivity", for the odd case. Full account of the route:
`rho_span`'s own toolkit docstring above. -/
theorem rho_span_odd {F : FermionIndex} {n : ℕ} (Tb : Midx F n → MMod F n)
    (hh : Homogeneous 1 Tb) (ho : ospCond 1 Tb) :
    ∃ c : OspBasis F n → ℚ, (∀ X, parity X ≠ 1 → c X = 0) ∧
      Tb = fun i => ∑ X : OspBasis F n, (c X) • rhoBasis X i := by
  refine ⟨cOdd Tb, cOdd_support Tb, ?_⟩
  set candSum : Midx F n → MMod F n := fun i => ∑ X : OspBasis F n, cOdd Tb X • rhoBasis X i
    with hcandSum
  have hDhom : Homogeneous 1 (Tb - candSum) :=
    Homogeneous_sub 1 Tb candSum hh (rhoCombo_homogeneous 1 (cOdd Tb) (cOdd_support Tb))
  have hDosp : ospCond 1 (Tb - candSum) :=
    ospCond_sub 1 Tb candSum ho (rhoCombo_ospCond 1 (cOdd Tb) (cOdd_support Tb))
  have hDinl : ∀ k : F.K, (Tb - candSum) (Sum.inl k) = 0 := by
    intro k
    funext j
    match j with
    | .inl k' =>
      change Tb (Sum.inl k) (Sum.inl k')
          - (∑ X : OspBasis F n, cOdd Tb X • rhoBasis X (Sum.inl k)) (Sum.inl k') = 0
      rw [cOdd_inl_inl Tb hh k k']
      simp
    | .inr u0 =>
      change Tb (Sum.inl k) (Sum.inr u0)
          - (∑ X : OspBasis F n, cOdd Tb X • rhoBasis X (Sum.inl k)) (Sum.inr u0) = 0
      rw [cOdd_inl_inr Tb k u0]
      simp
  have hDinr : ∀ u : I n, (Tb - candSum) (Sum.inr u) = 0 := by
    intro u
    funext j
    match j with
    | .inr u' =>
      by_contra hz
      have := hDhom (Sum.inr u) (Sum.inr u') hz
      simp only [pM] at this
      exact absurd this (by decide)
    | .inl k' =>
      have hospeq := hDosp (Sum.inr u) (Sum.inl (F.dual k'))
      rw [show gsign 1 (pM (Sum.inr u : Midx F n)) = -1 from by
        simp only [pM]; exact gsign_11] at hospeq
      rw [hDinl (F.dual k')] at hospeq
      simp only [Bpair_zero_right, smul_zero, add_zero] at hospeq
      rw [Bpair_eNM_inl] at hospeq
      rw [neg_eq_zero] at hospeq
      have hpick : (Tb - candSum) (Sum.inr u) (Sum.inl k') = 0 := by
        have h2 := hospeq
        rw [Finset.sum_eq_single k'] at h2
        · rwa [g_dual_right, ite_eq_left rfl, mul_one] at h2
        · intro b _ hb
          rw [g_dual_right, ite_eq_right hb, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      exact hpick
  funext i
  match i with
  | .inl k => funext j; have := hDinl k; exact sub_eq_zero.mp (congrFun this j)
  | .inr u => funext j; have := hDinr u; exact sub_eq_zero.mp (congrFun this j)

/-! ## `rho_span`'s even case (`p = 0`) -- the `S`-block

Unlike the odd case, `ospCond 0` does not couple the
`L`-block (`inr`-`inr`) to the `S`-block (`inl`-`inl`) -- `Bform`'s mixed values being
`0` gives no cross-block information, so there is no "determined by one half" bootstrap
here. Each block needs its OWN argument, directly from `ospCond 0 Tb`'s
self-consistency within that block, following one abstract shape: for a
matrix `A a b` satisfying `A a b = -ε · A (σ b) (σ a)` (an involution `σ`, `ε ∈ {±1}`),
`A` is recovered from its own key-ordered values. For the `S`-block (`ε = +1`, `σ =
F.dual`), this is `S_block_antisym` below (`Tb(inl a)(inl a'') = -Tb(inl(F.dual
a''))(inl(F.dual a))`) -- equivalently `Tb(inl a)(inl(F.dual b))` is a genuine
antisymmetric form in `(a,b)`, matching the strict order `F.key i < F.key j` `S`-kind's
own basis type uses (no diagonal). The `L`-block (`ε = -1`, `σ = Idual`, `Idual u :=
(u.1,!u.2)`) needs the `I n`/`J`-analogue -- structurally heavier: `J` is itself
antisymmetric (`J_antisymm`, unlike `F.g_symm`), the reindexing `J a (Idual b) = if a=b
then (if a.2 then -1 else 1) else 0` carries a sign depending on `a.2` (unlike
`g_dual_right`'s clean `+1`), and `IKey`'s own order is non-strict (`≤`, the diagonal
`u=v` is a genuine `L`-kind basis element, unlike `S`), so the "sum over ordered pairs =
half the full sum" identity needs the diagonal added back in, not excluded (the
`L`-block section below). -/

theorem Bpair_eNM_inl_left {F : FermionIndex} {n : ℕ} (k : F.K) (y : MMod F n) :
    Bpair (eNM (Sum.inl k)) y = -∑ c : F.K, y (Sum.inl c) * F.g k c := by
  unfold Bpair
  have hswap : (∑ i : Midx F n, ∑ j : Midx F n, (eNM (Sum.inl k : Midx F n)) i * y j * Bform i j)
      = ∑ i : Midx F n, (eNM (Sum.inl k : Midx F n)) i * ∑ j : Midx F n, y j * Bform i j := by
    apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hswap]
  have hone : (eNM (Sum.inl k : Midx F n) : MMod F n) (Sum.inl k) = 1 := by unfold eNM; simp
  have hcollapse :
    (∑ i : Midx F n, (eNM (Sum.inl k : Midx F n)) i * ∑ j : Midx F n, y j * Bform i j)
      = (eNM (Sum.inl k : Midx F n)) (Sum.inl k) * ∑ j : Midx F n, y j * Bform (Sum.inl k) j := by
    apply Finset.sum_eq_single (Sum.inl k : Midx F n)
    · intro b _ hb
      have hz : (eNM (Sum.inl k : Midx F n) : MMod F n) b = 0 := by
        unfold eNM; split_ifs with h
        · exact absurd h hb
        · rfl
      rw [hz, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hcollapse, hone, one_mul]
  have step2 : (∑ j : Midx F n, y j * Bform (Sum.inl k) j)
      = ∑ c : F.K, y (Sum.inl c) * Bform (Sum.inl k) (Sum.inl c)
        + ∑ b : I n, y (Sum.inr b) * Bform (Sum.inl k) (Sum.inr b) :=
    Fintype.sum_sum_type (fun j => y j * Bform (Sum.inl k) j)
  rw [step2]
  have hz : ∑ b : I n, y (Sum.inr b) * Bform (Sum.inl k) (Sum.inr b) = 0 := by
    apply Finset.sum_eq_zero; intro b _; unfold Bform; simp
  rw [hz, add_zero]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c _
  unfold Bform; ring

/-- **The `S`-block's own "twisted antisymmetry"**, from `ospCond 0 Tb` applied at
`(inl a, inl (F.dual a''))`: `Bpair_eNM_inl`/`Bpair_eNM_inl_left` expand both terms into
`F.K`-sums, and `g_dual_right` (evaluated at `a'' ↦ F.dual a''`, then the second term
reindexed via `F.dual`'s own bijectivity) collapses each to a single value. -/
theorem S_block_antisym {F : FermionIndex} {n : ℕ} (Tb : Midx F n → MMod F n)
    (ho : ospCond 0 Tb) (a a'' : F.K) :
    Tb (Sum.inl a) (Sum.inl a'') = -Tb (Sum.inl (F.dual a'')) (Sum.inl (F.dual a)) := by
  have heq := ho (Sum.inl a) (Sum.inl (F.dual a''))
  rw [gsign_zero_left, one_smul] at heq
  rw [Bpair_eNM_inl, Bpair_eNM_inl_left] at heq
  have hL : (∑ c : F.K, Tb (Sum.inl a) (Sum.inl c) * F.g c (F.dual a''))
      = Tb (Sum.inl a) (Sum.inl a'') := by
    rw [Finset.sum_eq_single a'']
    · rw [g_dual_right]; simp
    · intro b _ hb; rw [g_dual_right, ite_eq_right hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hR : (∑ c : F.K, Tb (Sum.inl (F.dual a'')) (Sum.inl c) * F.g a c)
      = Tb (Sum.inl (F.dual a'')) (Sum.inl (F.dual a)) := by
    have hreindex : (∑ c : F.K, Tb (Sum.inl (F.dual a'')) (Sum.inl c) * F.g a c)
        = ∑ c : F.K, Tb (Sum.inl (F.dual a'')) (Sum.inl (F.dual c)) * F.g a (F.dual c) := by
      apply Fintype.sum_bijective F.dual
      · exact Function.Involutive.bijective F.dual_dual
      · intro c; rw [F.dual_dual]
    rw [hreindex]
    rw [Finset.sum_eq_single a]
    · rw [g_dual_right]; simp
    · intro b _ hb; rw [g_dual_right, ite_eq_right (Ne.symm hb), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hL, hR] at heq
  linarith [heq]

/-- **General combinatorics**: for `f : F.K → F.K → ℚ` symmetric under swap
(`f j i = f i j`) with zero diagonal, the sum over `F.key`-ordered pairs equals half the
full double sum. Proved by partitioning `F.K × F.K` into the ordered, reverse-ordered,
and diagonal pieces (`Finset.sum_union` twice), the reverse piece equal to the ordered
piece by the swap bijection + `hsym`, the diagonal piece `0` by `hdiag`. -/
theorem sym_sum_split {F : FermionIndex} (f : F.K → F.K → ℚ)
    (hsym : ∀ i j, f j i = f i j) (hdiag : ∀ i, f i i = 0) :
    (∑ p : {q : F.K × F.K // F.key q.1 < F.key q.2}, f p.1.1 p.1.2)
      = (1/2 : ℚ) * ∑ i : F.K, ∑ j : F.K, f i j := by
  classical
  set A : Finset (F.K × F.K) := Finset.univ.filter (fun q => F.key q.1 < F.key q.2) with hA
  set B : Finset (F.K × F.K) := Finset.univ.filter (fun q => F.key q.2 < F.key q.1) with hB
  set C : Finset (F.K × F.K) := Finset.univ.filter (fun q => q.1 = q.2) with hC
  have hsub : (∑ p ∈ A, f p.1 p.2) = ∑ p : {q : F.K × F.K // F.key q.1 < F.key q.2},
    f p.1.1 p.1.2 :=
    Finset.sum_subtype A (fun x => by rw [hA]; simp) (fun p => f p.1 p.2)
  rw [← hsub]
  have hfull : (∑ i : F.K, ∑ j : F.K, f i j) = ∑ p : F.K × F.K, f p.1 p.2 :=
    (Fintype.sum_prod_type (fun p : F.K × F.K => f p.1 p.2)).symm
  rw [hfull]
  have hpart : (Finset.univ : Finset (F.K × F.K)) = A ∪ B ∪ C := by
    ext q
    simp only [hA, hB, hC, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro _
      rcases lt_trichotomy (F.key q.1) (F.key q.2) with h | h | h
      · left; left; exact h
      · right; exact F.key_injective h
      · left; right; exact h
    · intro _; trivial
  have hABdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro q hqA hqB
    rw [hA, Finset.mem_filter] at hqA
    rw [hB, Finset.mem_filter] at hqB
    omega
  have hABCdisj : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    intro q hqAB hqC
    rw [hC, Finset.mem_filter] at hqC
    rw [Finset.mem_union] at hqAB
    rcases hqAB with hqA | hqB
    · rw [hA, Finset.mem_filter] at hqA; rw [hqC.2] at hqA; exact absurd hqA.2 (lt_irrefl _)
    · rw [hB, Finset.mem_filter] at hqB; rw [hqC.2] at hqB; exact absurd hqB.2 (lt_irrefl _)
  have hsplit : (∑ p : F.K × F.K, f p.1 p.2)
      = (∑ p ∈ A, f p.1 p.2) + (∑ p ∈ B, f p.1 p.2) + ∑ p ∈ C, f p.1 p.2 := by
    show (∑ p ∈ (Finset.univ : Finset (F.K × F.K)), f p.1 p.2) = _
    rw [hpart, Finset.sum_union hABCdisj, Finset.sum_union hABdisj]
  rw [hsplit]
  have hBA : (∑ p ∈ B, f p.1 p.2) = ∑ p ∈ A, f p.1 p.2 := by
    apply Finset.sum_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1))
    · intro p hp
      rw [hB, Finset.mem_filter] at hp
      rw [hA, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hp.2⟩
    · intro p hp
      rw [hA, Finset.mem_filter] at hp
      rw [hB, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hp.2⟩
    · intro p _; simp
    · intro p _; simp
    · intro p _; exact hsym p.2 p.1
  have hCdiag : (∑ p ∈ C, f p.1 p.2) = ∑ i : F.K, f i i := by
    apply Finset.sum_nbij' (fun p => p.1) (fun i => (i, i))
    · intro p hp; exact Finset.mem_univ _
    · intro i _
      rw [hC, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, rfl⟩
    · intro p hp
      rw [hC, Finset.mem_filter] at hp
      exact Prod.ext rfl hp.2
    · intro i _; simp
    · intro p hp
      rw [hC, Finset.mem_filter] at hp
      congr 1
      exact hp.2.symm
  rw [hBA, hCdiag]
  have hz : ∑ i : F.K, f i i = 0 := by
    apply Finset.sum_eq_zero; intro i _; exact hdiag i
  rw [hz]
  ring

/-- **`candSum`'s `S`-part matches `Tb`'s ENTIRE `inl`-`inl` block**, at every `(a,a')`
pair, not just the diagnostic one: define `ĉ(i,j) := Tb(inl(F.dual j))(inl i)` (matching
`S_indep_full`'s own extraction formula, now defining rather than extracting), and
`f(i,j) := ĉ(i,j) • (rhoBasis`'s own `S`-kind kernel evaluated at `(a,a')`)`; `hantisym`
(from `S_block_antisym`) gives `ĉ(j,i) = -ĉ(i,j)`, and since the kernel is ALSO
antisymmetric under `i ↔ j`, their product `f` is genuinely symmetric --
`sym_sum_split` applies, reducing the target to computing `f`'s own full double sum
(`hFULL`), which collapses via the SAME `F.dual`-reindexing + `g_dual_right` used
throughout `rho_span_odd`, using `S_block_antisym` once more for the second half. -/
theorem cEven_S_inl_inl {F : FermionIndex} {n : ℕ} (Tb : Midx F n → MMod F n)
    (ho : ospCond 0 Tb) (a a' : F.K) :
    (∑ p : {q : F.K × F.K // F.key q.1 < F.key q.2},
        (Tb (Sum.inl (F.dual p.1.2)) (Sum.inl p.1.1))
          * (F.g p.1.2 a * (if a' = p.1.1 then (1:ℚ) else 0)
             - F.g p.1.1 a * (if a' = p.1.2 then (1:ℚ) else 0)))
      = Tb (Sum.inl a) (Sum.inl a') := by
  set ĉ : F.K → F.K → ℚ := fun i j => Tb (Sum.inl (F.dual j)) (Sum.inl i) with hĉ
  set f : F.K → F.K → ℚ := fun i j =>
    ĉ i j * (F.g j a * (if a' = i then (1:ℚ) else 0) - F.g i a * (if a' = j then (1:ℚ) else 0))
    with hf
  have hantisym : ∀ i j, ĉ j i = -ĉ i j := by
    intro i j
    have := S_block_antisym Tb ho (F.dual i) j
    rw [F.dual_dual] at this
    simpa [hĉ] using this
  have hsym : ∀ i j, f j i = f i j := by
    intro i j
    simp only [hf, hantisym i j]
    ring
  have hdiag : ∀ i, f i i = 0 := by intro i; simp [hf]
  have hkey := sym_sum_split f hsym hdiag
  have hgoal : (∑ p : {q : F.K × F.K // F.key q.1 < F.key q.2}, f p.1.1 p.1.2)
      = (∑ p : {q : F.K × F.K // F.key q.1 < F.key q.2},
          (Tb (Sum.inl (F.dual p.1.2)) (Sum.inl p.1.1))
            * (F.g p.1.2 a * (if a' = p.1.1 then (1:ℚ) else 0)
               - F.g p.1.1 a * (if a' = p.1.2 then (1:ℚ) else 0))) := rfl
  rw [← hgoal, hkey]
  have hFULL : (∑ i : F.K, ∑ j : F.K, f i j) = 2 * Tb (Sum.inl a) (Sum.inl a') := by
    have hdist : (∑ i : F.K, ∑ j : F.K, f i j)
        = (∑ i : F.K, ∑ j : F.K,
            Tb (Sum.inl (F.dual j)) (Sum.inl i) * F.g j a * (if a' = i then (1:ℚ) else 0))
          - ∑ i : F.K, ∑ j : F.K,
            Tb (Sum.inl (F.dual j)) (Sum.inl i) * F.g i a * (if a' = j then (1:ℚ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _
      simp only [hf, hĉ]; ring
    rw [hdist]
    have piece1 : (∑ i : F.K, ∑ j : F.K,
          Tb (Sum.inl (F.dual j)) (Sum.inl i) * F.g j a * (if a' = i then (1:ℚ) else 0))
        = Tb (Sum.inl a) (Sum.inl a') := by
      have hfac : (∑ i : F.K, ∑ j : F.K,
            Tb (Sum.inl (F.dual j)) (Sum.inl i) * F.g j a * (if a' = i then (1:ℚ) else 0))
          = ∑ i : F.K, (if a' = i then (1:ℚ) else 0)
              * ∑ j : F.K, Tb (Sum.inl (F.dual j)) (Sum.inl i) * F.g j a := by
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      rw [hfac, Finset.sum_eq_single a']
      · rw [ite_eq_left rfl, one_mul]
        have hreindex : (∑ j : F.K, Tb (Sum.inl (F.dual j)) (Sum.inl a') * F.g j a)
            = ∑ j : F.K, Tb (Sum.inl j) (Sum.inl a') * F.g (F.dual j) a := by
          apply Fintype.sum_bijective F.dual
          · exact Function.Involutive.bijective F.dual_dual
          · intro j; rw [F.dual_dual]
        rw [hreindex, Finset.sum_eq_single a]
        · rw [F.g_symm, g_dual_right]; simp
        · intro b _ hb; rw [F.g_symm, g_dual_right, ite_eq_right (Ne.symm hb), mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro b _ hb; rw [ite_eq_right (Ne.symm hb), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    have piece2 : (∑ i : F.K, ∑ j : F.K,
          Tb (Sum.inl (F.dual j)) (Sum.inl i) * F.g i a * (if a' = j then (1:ℚ) else 0))
        = -Tb (Sum.inl a) (Sum.inl a') := by
      have hswap : (∑ i : F.K, ∑ j : F.K,
            Tb (Sum.inl (F.dual j)) (Sum.inl i) * F.g i a * (if a' = j then (1:ℚ) else 0))
          = ∑ j : F.K, (if a' = j then (1:ℚ) else 0)
              * ∑ i : F.K, Tb (Sum.inl (F.dual j)) (Sum.inl i) * F.g i a := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      rw [hswap, Finset.sum_eq_single a']
      · rw [ite_eq_left rfl, one_mul]
        have hreindex : (∑ i : F.K, Tb (Sum.inl (F.dual a')) (Sum.inl i) * F.g i a)
            = ∑ i : F.K, Tb (Sum.inl (F.dual a')) (Sum.inl (F.dual i)) * F.g (F.dual i) a := by
          apply Fintype.sum_bijective F.dual
          · exact Function.Involutive.bijective F.dual_dual
          · intro i; rw [F.dual_dual]
        rw [hreindex, Finset.sum_eq_single a]
        · rw [F.g_symm, g_dual_right, ite_eq_left rfl, mul_one, S_block_antisym Tb ho a a']
          ring
        · intro b _ hb; rw [F.g_symm, g_dual_right, ite_eq_right (Ne.symm hb), mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro b _ hb; rw [ite_eq_right (Ne.symm hb), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [piece1, piece2]; ring
  rw [hFULL]; ring

/-! ## `L`-block

`Bpair_eNM_inr`/`Bpair_eNM_inr_left` are the `I n`-block analogues of
`Bpair_eNM_inl`/`_left` (no negation, since `Bform`'s `inr`-`inr` value is `+J`, not
`-F.g`). `Idual u := (u.1,!u.2)` is the `I n`-analogue of `F.dual`; `J_dual_eq` is `J`'s
own duality fact, `J n a (Idual b) = if a=b then (if a.2 then -1 else 1) else 0` --
unlike `g_dual_right`, the value carries a sign depending on `a.2` (from `J`'s own
antisymmetry, `J_antisymm`, unlike `F.g_symm`'s plain symmetry). `L_block_relation` is
the `L`-block's own twisted relation from `ospCond 0 Tb`, derived exactly as
`S_block_antisym` was, via `Bpair_eNM_inr`/`_left` + `J_dual_eq` + `Idual`-bijective
reindexing. `sym_sum_split_I` is `sym_sum_split`'s own proof verbatim over `I n`/`IKey`
in place of `F.K`/`F.key` (the proof is purely combinatorial, using only
`IKey_injective`, no `F`-specific structure); the two could be factored into one lemma over
an abstract `(ι, key)`.

**The coefficient formula**: writing `CFun i j := -2·J(Idual j, j)·Tb(inr(Idual j))(inr i)` (the
`L`-block's own analogue of the `S`-block's `ĉ`, `J(Idual j,j)` supplying the sign
`g_dual_right` didn't need to), `CFun` is a genuinely SYMMETRIC function of `(i,j)`
(`CFun_symm`, from `L_block_relation`) -- UNLIKE the naive `ĉ` alone, whose own symmetry is merely
"twisted" (`ĉ(j,i) = s(i)s(j)·ĉ(i,j)`). The `L`-kind coefficient is then `CFun i j` at off-diagonal
pairs (`IKey i < IKey j`) and `(1/2)·CFun i i` at the diagonal (`Sof`/`rhoBasis`'s own missing `1/2`
there) -- `cEven_L_inr_inr` proves this reconstructs `Tb`'s ENTIRE `inr`-`inr` block, via
`sym_sum_full_I` (`sym_sum_split_I` generalized to drop the zero-diagonal hypothesis:
`Σ_full = 2·Σ_{i<j} + Σ_diag`, for any genuinely symmetric `f`) applied to `CFun · Kernel` (both
factors symmetric) plus `CFun_full_sum` (the `Σ_full` value is exactly `2·Tb(w,u)`, by the SAME
two-piece `J`/`Idual`-reindexing argument `rho_span_odd`'s own `cOdd_inl_inr` used, now doubled
since `J`'s own antisymmetry surfaces an extra sign at each collapse). -/

theorem Bpair_eNM_inr {F : FermionIndex} {n : ℕ} (x : MMod F n) (w : I n) :
    Bpair x (eNM (Sum.inr w)) = ∑ u : I n, x (Sum.inr u) * J n u w := by
  unfold Bpair
  have step1 : (∑ i : Midx F n, ∑ j : Midx F n, x i * (eNM (Sum.inr w : Midx F n)) j * Bform i j)
      = ∑ i : Midx F n, x i * Bform i (Sum.inr w) := by
    apply Finset.sum_congr rfl
    intro i _
    have hone : (eNM (Sum.inr w : Midx F n) : MMod F n) (Sum.inr w) = 1 := by unfold eNM; simp
    have hcollapse : (∑ j : Midx F n, x i * (eNM (Sum.inr w : Midx F n)) j * Bform i j)
        = x i * (eNM (Sum.inr w : Midx F n)) (Sum.inr w) * Bform i (Sum.inr w) := by
      apply Finset.sum_eq_single (Sum.inr w : Midx F n)
      · intro b _ hb
        have hz : (eNM (Sum.inr w : Midx F n) : MMod F n) b = 0 := by
          unfold eNM; split_ifs with h
          · exact absurd h hb
          · rfl
        rw [hz, mul_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hcollapse, hone, mul_one]
  rw [step1]
  have step2 : (∑ i : Midx F n, x i * Bform i (Sum.inr w))
      = ∑ a : F.K, x (Sum.inl a) * Bform (Sum.inl a) (Sum.inr w)
        + ∑ u : I n, x (Sum.inr u) * Bform (Sum.inr u) (Sum.inr w) :=
    Fintype.sum_sum_type (fun i => x i * Bform i (Sum.inr w))
  rw [step2]
  have hz : ∑ a : F.K, x (Sum.inl a) * Bform (Sum.inl a) (Sum.inr w) = 0 := by
    apply Finset.sum_eq_zero; intro a _; unfold Bform; simp
  rw [hz, zero_add]
  apply Finset.sum_congr rfl
  intro u _
  unfold Bform; rfl

theorem Bpair_eNM_inr_left {F : FermionIndex} {n : ℕ} (w : I n) (y : MMod F n) :
    Bpair (eNM (Sum.inr w)) y = ∑ u : I n, y (Sum.inr u) * J n w u := by
  unfold Bpair
  have hswap : (∑ i : Midx F n, ∑ j : Midx F n, (eNM (Sum.inr w : Midx F n)) i * y j * Bform i j)
      = ∑ i : Midx F n, (eNM (Sum.inr w : Midx F n)) i * ∑ j : Midx F n, y j * Bform i j := by
    apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hswap]
  have hone : (eNM (Sum.inr w : Midx F n) : MMod F n) (Sum.inr w) = 1 := by unfold eNM; simp
  have hcollapse :
    (∑ i : Midx F n, (eNM (Sum.inr w : Midx F n)) i * ∑ j : Midx F n, y j * Bform i j)
      = (eNM (Sum.inr w : Midx F n)) (Sum.inr w) * ∑ j : Midx F n, y j * Bform (Sum.inr w) j := by
    apply Finset.sum_eq_single (Sum.inr w : Midx F n)
    · intro b _ hb
      have hz : (eNM (Sum.inr w : Midx F n) : MMod F n) b = 0 := by
        unfold eNM; split_ifs with h
        · exact absurd h hb
        · rfl
      rw [hz, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hcollapse, hone, one_mul]
  have step2 : (∑ j : Midx F n, y j * Bform (Sum.inr w) j)
      = ∑ a : F.K, y (Sum.inl a) * Bform (Sum.inr w) (Sum.inl a)
        + ∑ u : I n, y (Sum.inr u) * Bform (Sum.inr w) (Sum.inr u) :=
    Fintype.sum_sum_type (fun j => y j * Bform (Sum.inr w) j)
  rw [step2]
  have hz : ∑ a : F.K, y (Sum.inl a) * Bform (Sum.inr w) (Sum.inl a) = 0 := by
    apply Finset.sum_eq_zero; intro a _; unfold Bform; simp
  rw [hz, zero_add]
  apply Finset.sum_congr rfl
  intro u _
  unfold Bform; rfl

def Idual {n : ℕ} (u : I n) : I n := (u.1, !u.2)

theorem Idual_Idual {n : ℕ} (u : I n) : Idual (Idual u) = u := by
  unfold Idual; simp

theorem J_dual_eq {n : ℕ} (a b : I n) :
    J n a (Idual b) = if a = b then (if a.2 then (-1:ℚ) else 1) else 0 := by
  obtain ⟨ka, ba⟩ := a
  obtain ⟨kb, bb⟩ := b
  unfold Idual J
  cases ba <;> cases bb <;> simp_all

/-- **The `L`-block's own "twisted relation"**, from `ospCond 0 Tb` applied at `(inr u,
inr (Idual v))`: mirrors `S_block_antisym`'s own derivation, via
`Bpair_eNM_inr`/`Bpair_eNM_inr_left` and `J_dual_eq` (evaluated at `v ↦ Idual v`, then
the second term reindexed via `Idual`'s own bijectivity). Unlike `S_block_antisym`,
carries the `s(v)`/`s(u)` sign factors from `J_dual_eq`'s own parity-dependent value. -/
theorem L_block_relation {F : FermionIndex} {n : ℕ} (Tb : Midx F n → MMod F n)
    (ho : ospCond 0 Tb) (u v : I n) :
    Tb (Sum.inr u) (Sum.inr v) * (if v.2 then (-1:ℚ) else 1)
      + Tb (Sum.inr (Idual v)) (Sum.inr (Idual u)) * (if u.2 then (-1:ℚ) else 1) = 0 := by
  have heq := ho (Sum.inr u) (Sum.inr (Idual v))
  rw [gsign_zero_left, one_smul] at heq
  rw [Bpair_eNM_inr, Bpair_eNM_inr_left] at heq
  have hL : (∑ w : I n, Tb (Sum.inr u) (Sum.inr w) * J n w (Idual v))
      = Tb (Sum.inr u) (Sum.inr v) * (if v.2 then (-1:ℚ) else 1) := by
    rw [Finset.sum_eq_single v]
    · rw [J_dual_eq]; simp
    · intro b _ hb; rw [J_dual_eq, ite_eq_right hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hR : (∑ w : I n, Tb (Sum.inr (Idual v)) (Sum.inr w) * J n u w)
      = Tb (Sum.inr (Idual v)) (Sum.inr (Idual u)) * (if u.2 then (-1:ℚ) else 1) := by
    have hreindex : (∑ w : I n, Tb (Sum.inr (Idual v)) (Sum.inr w) * J n u w)
        = ∑ w : I n, Tb (Sum.inr (Idual v)) (Sum.inr (Idual w)) * J n u (Idual w) := by
      apply Fintype.sum_bijective Idual
      · exact Function.Involutive.bijective Idual_Idual
      · intro w; rw [Idual_Idual]
    rw [hreindex]
    rw [Finset.sum_eq_single u]
    · rw [J_dual_eq]; simp
    · intro b _ hb; rw [J_dual_eq, ite_eq_right (Ne.symm hb), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hL, hR] at heq
  linarith [heq]

/-- `sym_sum_split`'s own proof, verbatim, over `I n`/`IKey` in place of `F.K`/`F.key`
(purely combinatorial -- only `IKey_injective` is used, no other `F`-specific
structure). Both could be factored into one lemma over an abstract `(ι, key)`
pair. -/
theorem sym_sum_split_I {n : ℕ} (f : I n → I n → ℚ)
    (hsym : ∀ i j, f j i = f i j) (hdiag : ∀ i, f i i = 0) :
    (∑ p : {q : I n × I n // IKey q.1 < IKey q.2}, f p.1.1 p.1.2)
      = (1/2 : ℚ) * ∑ i : I n, ∑ j : I n, f i j := by
  classical
  set A : Finset (I n × I n) := Finset.univ.filter (fun q => IKey q.1 < IKey q.2) with hA
  set B : Finset (I n × I n) := Finset.univ.filter (fun q => IKey q.2 < IKey q.1) with hB
  set C : Finset (I n × I n) := Finset.univ.filter (fun q => q.1 = q.2) with hC
  have hsub : (∑ p ∈ A, f p.1 p.2) = ∑ p : {q : I n × I n // IKey q.1 < IKey q.2}, f p.1.1 p.1.2 :=
    Finset.sum_subtype A (fun x => by rw [hA]; simp) (fun p => f p.1 p.2)
  rw [← hsub]
  have hfull : (∑ i : I n, ∑ j : I n, f i j) = ∑ p : I n × I n, f p.1 p.2 :=
    (Fintype.sum_prod_type (fun p : I n × I n => f p.1 p.2)).symm
  rw [hfull]
  have hpart : (Finset.univ : Finset (I n × I n)) = A ∪ B ∪ C := by
    ext q
    simp only [hA, hB, hC, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro _
      rcases lt_trichotomy (IKey q.1) (IKey q.2) with h | h | h
      · left; left; exact h
      · right; exact IKey_injective h
      · left; right; exact h
    · intro _; trivial
  have hABdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro q hqA hqB
    rw [hA, Finset.mem_filter] at hqA
    rw [hB, Finset.mem_filter] at hqB
    omega
  have hABCdisj : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    intro q hqAB hqC
    rw [hC, Finset.mem_filter] at hqC
    rw [Finset.mem_union] at hqAB
    rcases hqAB with hqA | hqB
    · rw [hA, Finset.mem_filter] at hqA; rw [hqC.2] at hqA; exact absurd hqA.2 (lt_irrefl _)
    · rw [hB, Finset.mem_filter] at hqB; rw [hqC.2] at hqB; exact absurd hqB.2 (lt_irrefl _)
  have hsplit : (∑ p : I n × I n, f p.1 p.2)
      = (∑ p ∈ A, f p.1 p.2) + (∑ p ∈ B, f p.1 p.2) + ∑ p ∈ C, f p.1 p.2 := by
    show (∑ p ∈ (Finset.univ : Finset (I n × I n)), f p.1 p.2) = _
    rw [hpart, Finset.sum_union hABCdisj, Finset.sum_union hABdisj]
  rw [hsplit]
  have hBA : (∑ p ∈ B, f p.1 p.2) = ∑ p ∈ A, f p.1 p.2 := by
    apply Finset.sum_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1))
    · intro p hp
      rw [hB, Finset.mem_filter] at hp
      rw [hA, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hp.2⟩
    · intro p hp
      rw [hA, Finset.mem_filter] at hp
      rw [hB, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hp.2⟩
    · intro p _; simp
    · intro p _; simp
    · intro p _; exact hsym p.2 p.1
  have hCdiag : (∑ p ∈ C, f p.1 p.2) = ∑ i : I n, f i i := by
    apply Finset.sum_nbij' (fun p => p.1) (fun i => (i, i))
    · intro p hp; exact Finset.mem_univ _
    · intro i _
      rw [hC, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, rfl⟩
    · intro p hp
      rw [hC, Finset.mem_filter] at hp
      exact Prod.ext rfl hp.2
    · intro i _; simp
    · intro p hp
      rw [hC, Finset.mem_filter] at hp
      congr 1
      exact hp.2.symm
  rw [hBA, hCdiag]
  have hz : ∑ i : I n, f i i = 0 := by
    apply Finset.sum_eq_zero; intro i _; exact hdiag i
  rw [hz]
  ring

theorem J_Idual_left {n : ℕ} (b w : I n) :
    J n (Idual b) w = if w = b then (if b.2 then (1:ℚ) else -1) else 0 := by
  rw [J_antisymm (Idual b) w, J_dual_eq]
  by_cases h : w = b
  · subst h; cases w.2 <;> simp
  · simp [h]

/-- `-2·J(Idual j,j)·Tb(inr(Idual j))(inr i)` -- the `L`-block's own coefficient
kernel, the analogue of the `S`-block's `ĉ`. -/
def CFun {F : FermionIndex} {n : ℕ} (Tb : Midx F n → MMod F n) (i j : I n) : ℚ :=
  -2 * J n (Idual j) j * Tb (Sum.inr (Idual j)) (Sum.inr i)

/-- **`CFun` is genuinely symmetric** (unlike the raw `ĉ` it is built from, whose own
symmetry is only "twisted" by `s(i)s(j)`): the `J(Idual j,j)`/`J(Idual i,i)` sign
factors exactly cancel the twist, from `L_block_relation` applied at `(Idual i, j)`. -/
theorem CFun_symm {F : FermionIndex} {n : ℕ} (Tb : Midx F n → MMod F n)
    (L_block_relation : ∀ u v : I n, Tb (Sum.inr u) (Sum.inr v) * (if v.2 then (-1:ℚ) else 1)
        + Tb (Sum.inr (Idual v)) (Sum.inr (Idual u)) * (if u.2 then (-1:ℚ) else 1) = 0)
    (i j : I n) : CFun Tb j i = CFun Tb i j := by
  unfold CFun
  have hJ1 : J n (Idual i) i = if i.2 then (1:ℚ) else -1 := by
    have := J_Idual_left i i; simpa using this
  have hJ2 : J n (Idual j) j = if j.2 then (1:ℚ) else -1 := by
    have := J_Idual_left j j; simpa using this
  rw [hJ1, hJ2]
  have h1 := L_block_relation (Idual i) j
  rw [Idual_Idual] at h1
  have hIdi : (Idual i).2 = !i.2 := rfl
  rw [hIdi] at h1
  rcases Bool.eq_false_or_eq_true i.2 with hi | hi <;>
    rcases Bool.eq_false_or_eq_true j.2 with hj | hj <;>
    simp [hi, hj] at h1 ⊢ <;> linarith [h1]

/-- **`CFun`'s own full sum against the `rhoBasis(L)`-kernel is `2·Tb(w,u)`** -- the
`L`-block's analogue of `rho_span_odd`'s own `cOdd_inl_inr` computation, now doubled
(and with an extra `J`-antisymmetry sign layer at each collapse, from `J`'s own
antisymmetry vs. `F.g`'s symmetry). -/
theorem CFun_full_sum {F : FermionIndex} {n : ℕ} (Tb : Midx F n → MMod F n)
    (L_block_relation : ∀ u v : I n, Tb (Sum.inr u) (Sum.inr v) * (if v.2 then (-1:ℚ) else 1)
        + Tb (Sum.inr (Idual v)) (Sum.inr (Idual u)) * (if u.2 then (-1:ℚ) else 1) = 0)
    (w u : I n) :
    (∑ i : I n, ∑ j : I n, CFun Tb i j
          * ((1/2 : ℚ) * (J n j w * (if u = i then 1 else 0) + J n i w * (if u = j then 1 else 0))))
      = 2 * Tb (Sum.inr w) (Sum.inr u) := by
  unfold CFun
  have hdist : (∑ i : I n, ∑ j : I n,
        (-2 * J n (Idual j) j * Tb (Sum.inr (Idual j)) (Sum.inr i))
          * ((1/2 : ℚ) * (J n j w * (if u = i then 1 else 0) + J n i w * (if u = j then 1 else 0))))
      = (∑ i : I n, ∑ j : I n,
          (-(J n (Idual j) j * Tb (Sum.inr (Idual j)) (Sum.inr i) * J n j w)) *
            (if u = i then 1 else 0))
        + (∑ i : I n, ∑ j : I n,
          (-(J n (Idual j) j * Tb (Sum.inr (Idual j)) (Sum.inr i) * J n i w)) *
            (if u = j then 1 else 0)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hdist]
  have piece1 : (∑ i : I n, ∑ j : I n,
        (-(J n (Idual j) j * Tb (Sum.inr (Idual j)) (Sum.inr i) * J n j w)) *
          (if u = i then 1 else 0))
      = Tb (Sum.inr w) (Sum.inr u) := by
    have hfac : (∑ i : I n, ∑ j : I n,
          (-(J n (Idual j) j * Tb (Sum.inr (Idual j)) (Sum.inr i) * J n j w)) *
            (if u = i then 1 else 0))
        = ∑ i : I n, (if u = i then (1:ℚ) else 0)
            * ∑ j : I n, (-(J n (Idual j) j * Tb (Sum.inr (Idual j)) (Sum.inr i) * J n j w)) := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    rw [hfac, Finset.sum_eq_single u]
    · rw [ite_eq_left rfl, one_mul]
      have hreindex : (∑ j : I n,
            -(J n (Idual j) j * Tb (Sum.inr (Idual j)) (Sum.inr u) * J n j w))
          = ∑ j : I n, -(J n j (Idual j) * Tb (Sum.inr j) (Sum.inr u) * J n (Idual j) w) := by
        apply Fintype.sum_bijective Idual
        · exact Function.Involutive.bijective Idual_Idual
        · intro j; rw [Idual_Idual]
      rw [hreindex]
      rw [Finset.sum_eq_single w]
      · have h1 : J n w (Idual w) = if w.2 then (-1:ℚ) else 1 := by
          have := J_dual_eq w w; simpa using this
        have h2 : J n (Idual w) w = if w.2 then (1:ℚ) else -1 := by
          have := J_Idual_left w w; simpa using this
        rw [h1, h2]
        cases w.2 <;> simp
      · intro b _ hb
        rw [J_Idual_left, ite_eq_right (Ne.symm hb)]
        ring
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro b _ hb; rw [ite_eq_right (Ne.symm hb), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have piece2 : (∑ i : I n, ∑ j : I n,
        (-(J n (Idual j) j * Tb (Sum.inr (Idual j)) (Sum.inr i) * J n i w)) *
          (if u = j then 1 else 0))
      = Tb (Sum.inr w) (Sum.inr u) := by
    have hswap : (∑ i : I n, ∑ j : I n,
          (-(J n (Idual j) j * Tb (Sum.inr (Idual j)) (Sum.inr i) * J n i w)) *
            (if u = j then 1 else 0))
        = ∑ j : I n, (if u = j then (1:ℚ) else 0)
            * ∑ i : I n, (-(J n (Idual j) j * Tb (Sum.inr (Idual j)) (Sum.inr i) * J n i w)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [hswap, Finset.sum_eq_single u]
    · rw [ite_eq_left rfl, one_mul]
      have hstep : (∑ i : I n, -(J n (Idual u) u * Tb (Sum.inr (Idual u)) (Sum.inr i) * J n i w))
          = -(J n (Idual u) u) * ∑ i : I n, Tb (Sum.inr (Idual u)) (Sum.inr i) * J n i w := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      rw [hstep]
      have hreindex : (∑ i : I n, Tb (Sum.inr (Idual u)) (Sum.inr i) * J n i w)
          = ∑ i : I n, Tb (Sum.inr (Idual u)) (Sum.inr (Idual i)) * J n (Idual i) w := by
        apply Fintype.sum_bijective Idual
        · exact Function.Involutive.bijective Idual_Idual
        · intro i; rw [Idual_Idual]
      rw [hreindex]
      have hcollapse : (∑ i : I n,
            Tb (Sum.inr (Idual u)) (Sum.inr (Idual i)) * J n (Idual i) w)
          = Tb (Sum.inr (Idual u)) (Sum.inr (Idual w)) * J n (Idual w) w := by
        rw [Finset.sum_eq_single w]
        · intro b _ hb
          have := J_Idual_left b w
          rw [ite_eq_right (Ne.symm hb)] at this
          rw [this]; ring
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hcollapse]
      have hL := L_block_relation w u
      have h3 : J n (Idual u) u = if u.2 then (1:ℚ) else -1 := by
        have := J_Idual_left u u; simpa using this
      have h4 : J n (Idual w) w = if w.2 then (1:ℚ) else -1 := by
        have := J_Idual_left w w; simpa using this
      rw [h3, h4]
      rcases Bool.eq_false_or_eq_true u.2 with hu | hu <;>
        rcases Bool.eq_false_or_eq_true w.2 with hw | hw <;>
        simp [hu, hw] at hL ⊢ <;> linarith [hL]
    · intro b _ hb; rw [ite_eq_right (Ne.symm hb), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [piece1, piece2]; ring

/-- `sym_sum_split_I` with the zero-diagonal hypothesis dropped: for ANY genuinely
symmetric `f`, the full double sum is twice the ordered-pair sum plus the diagonal sum
(`sym_sum_split_I`'s own proof, minus the final "diagonal is `0`" simplification). -/
theorem sym_sum_full_I {n : ℕ} (f : I n → I n → ℚ) (hsym : ∀ i j, f j i = f i j) :
    (∑ i : I n, ∑ j : I n, f i j)
      = 2 * (∑ p : {q : I n × I n // IKey q.1 < IKey q.2}, f p.1.1 p.1.2)
        + ∑ i : I n, f i i := by
  classical
  set A : Finset (I n × I n) := Finset.univ.filter (fun q => IKey q.1 < IKey q.2) with hA
  set B : Finset (I n × I n) := Finset.univ.filter (fun q => IKey q.2 < IKey q.1) with hB
  set C : Finset (I n × I n) := Finset.univ.filter (fun q => q.1 = q.2) with hC
  have hsub : (∑ p ∈ A, f p.1 p.2) = ∑ p : {q : I n × I n // IKey q.1 < IKey q.2}, f p.1.1 p.1.2 :=
    Finset.sum_subtype A (fun x => by rw [hA]; simp) (fun p => f p.1 p.2)
  have hfull : (∑ i : I n, ∑ j : I n, f i j) = ∑ p : I n × I n, f p.1 p.2 :=
    (Fintype.sum_prod_type (fun p : I n × I n => f p.1 p.2)).symm
  rw [hfull]
  have hpart : (Finset.univ : Finset (I n × I n)) = A ∪ B ∪ C := by
    ext q
    simp only [hA, hB, hC, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro _
      rcases lt_trichotomy (IKey q.1) (IKey q.2) with h | h | h
      · left; left; exact h
      · right; exact IKey_injective h
      · left; right; exact h
    · intro _; trivial
  have hABdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro q hqA hqB
    rw [hA, Finset.mem_filter] at hqA
    rw [hB, Finset.mem_filter] at hqB
    omega
  have hABCdisj : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    intro q hqAB hqC
    rw [hC, Finset.mem_filter] at hqC
    rw [Finset.mem_union] at hqAB
    rcases hqAB with hqA | hqB
    · rw [hA, Finset.mem_filter] at hqA; rw [hqC.2] at hqA; exact absurd hqA.2 (lt_irrefl _)
    · rw [hB, Finset.mem_filter] at hqB; rw [hqC.2] at hqB; exact absurd hqB.2 (lt_irrefl _)
  have hsplit : (∑ p : I n × I n, f p.1 p.2)
      = (∑ p ∈ A, f p.1 p.2) + (∑ p ∈ B, f p.1 p.2) + ∑ p ∈ C, f p.1 p.2 := by
    show (∑ p ∈ (Finset.univ : Finset (I n × I n)), f p.1 p.2) = _
    rw [hpart, Finset.sum_union hABCdisj, Finset.sum_union hABdisj]
  rw [hsplit]
  have hBA : (∑ p ∈ B, f p.1 p.2) = ∑ p ∈ A, f p.1 p.2 := by
    apply Finset.sum_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1))
    · intro p hp
      rw [hB, Finset.mem_filter] at hp
      rw [hA, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hp.2⟩
    · intro p hp
      rw [hA, Finset.mem_filter] at hp
      rw [hB, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hp.2⟩
    · intro p _; simp
    · intro p _; simp
    · intro p _; exact hsym p.2 p.1
  have hCdiag : (∑ p ∈ C, f p.1 p.2) = ∑ i : I n, f i i := by
    apply Finset.sum_nbij' (fun p => p.1) (fun i => (i, i))
    · intro p hp; exact Finset.mem_univ _
    · intro i _
      rw [hC, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, rfl⟩
    · intro p hp
      rw [hC, Finset.mem_filter] at hp
      exact Prod.ext rfl hp.2
    · intro i _; simp
    · intro p hp
      rw [hC, Finset.mem_filter] at hp
      congr 1
      exact hp.2.symm
  rw [hBA, hCdiag, hsub]
  ring

/-- **`candSum`'s `L`-part matches `Tb`'s ENTIRE `inr`-`inr` block**, at every `(w,u)`
pair: the `L`-kind coefficient is `CFun Tb p.1.1 p.1.2` at off-diagonal pairs and
`(1/2)·CFun Tb p.1.1 p.1.1` at the diagonal (mirroring `Sof`/`rhoBasis`'s own missing
`1/2` there). Splits the `≤`-subtype sum into its `<` and `=` pieces (mirroring
`sym_sum_full_I`'s own internal 3-way partition, but keeping the diagonal separate
since its own coefficient has the extra `1/2`), applies `sym_sum_full_I` to
`g := CFun Tb · Kernel` (symmetric, since both factors are: `CFun_symm`, and the
`rhoBasis(L)`-kernel `K(i,j;w,u) := (1/2)(J j w [u=i] + J i w [u=j])` is symmetric by
inspection), then `CFun_full_sum` gives the full sum directly, and the `(1/2)` factors
cancel exactly. -/
theorem cEven_L_inr_inr {F : FermionIndex} {n : ℕ} (Tb : Midx F n → MMod F n)
    (L_block_relation : ∀ u v : I n, Tb (Sum.inr u) (Sum.inr v) * (if v.2 then (-1:ℚ) else 1)
        + Tb (Sum.inr (Idual v)) (Sum.inr (Idual u)) * (if u.2 then (-1:ℚ) else 1) = 0)
    (w u : I n) :
    (∑ p : {q : I n × I n // IKey q.1 ≤ IKey q.2},
        (if p.1.1 = p.1.2 then (1/2 : ℚ) * CFun Tb p.1.1 p.1.2 else CFun Tb p.1.1 p.1.2)
          * ((1/2 : ℚ) * (J n p.1.2 w * (if u = p.1.1 then 1 else 0)
              + J n p.1.1 w * (if u = p.1.2 then 1 else 0))))
      = Tb (Sum.inr w) (Sum.inr u) := by
  set K : I n → I n → ℚ := fun i j =>
    (1/2 : ℚ) * (J n j w * (if u = i then 1 else 0) + J n i w * (if u = j then 1 else 0)) with hK
  set g : I n → I n → ℚ := fun i j => CFun Tb i j * K i j with hg
  have hKsym : ∀ i j, K j i = K i j := by intro i j; simp only [hK]; ring
  have hgsym : ∀ i j, g j i = g i j := by
    intro i j; simp only [hg]; rw [CFun_symm Tb L_block_relation, hKsym]
  have hsplit : (∑ p : {q : I n × I n // IKey q.1 ≤ IKey q.2},
        (if p.1.1 = p.1.2 then (1/2 : ℚ) * CFun Tb p.1.1 p.1.2 else CFun Tb p.1.1 p.1.2)
          * K p.1.1 p.1.2)
      = (∑ p : {q : I n × I n // IKey q.1 < IKey q.2}, g p.1.1 p.1.2)
        + (1/2 : ℚ) * ∑ i : I n, g i i := by
    classical
    set Ale : Finset (I n × I n) := Finset.univ.filter (fun q => IKey q.1 ≤ IKey q.2) with hAle
    set Alt : Finset (I n × I n) := Finset.univ.filter (fun q => IKey q.1 < IKey q.2) with hAlt
    set Aeq : Finset (I n × I n) := Finset.univ.filter (fun q => q.1 = q.2) with hAeq
    have hsub : (∑ p ∈ Ale,
          (if p.1 = p.2 then (1/2:ℚ) * CFun Tb p.1 p.2 else CFun Tb p.1 p.2) * K p.1 p.2)
        = ∑ p : {q : I n × I n // IKey q.1 ≤ IKey q.2},
            (if p.1.1 = p.1.2 then (1/2:ℚ) * CFun Tb p.1.1 p.1.2 else CFun Tb p.1.1 p.1.2)
              * K p.1.1 p.1.2 :=
      Finset.sum_subtype Ale (fun x => by rw [hAle]; simp)
        (fun p => (if p.1 = p.2 then (1/2:ℚ) * CFun Tb p.1 p.2 else CFun Tb p.1 p.2) * K p.1 p.2)
    rw [← hsub]
    have hsub2 : (∑ p ∈ Alt, g p.1 p.2) = ∑ p : {q : I n × I n // IKey q.1 < IKey q.2},
      g p.1.1 p.1.2 :=
      Finset.sum_subtype Alt (fun x => by rw [hAlt]; simp) (fun p => g p.1 p.2)
    rw [← hsub2]
    have hpart : Ale = Alt ∪ Aeq := by
      ext q
      simp only [hAle, hAlt, hAeq, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        rcases lt_or_eq_of_le h with h1 | h1
        · left; exact h1
        · right; exact IKey_injective h1
      · rintro (h | h)
        · exact le_of_lt h
        · rw [h]
    have hdisj : Disjoint Alt Aeq := by
      rw [Finset.disjoint_left]
      intro q hq1 hq2
      rw [hAlt, Finset.mem_filter] at hq1
      rw [hAeq, Finset.mem_filter] at hq2
      rw [hq2.2] at hq1
      exact absurd hq1.2 (lt_irrefl _)
    have hsplit2 : (∑ p ∈ Ale,
          (if p.1 = p.2 then (1/2:ℚ) * CFun Tb p.1 p.2 else CFun Tb p.1 p.2) * K p.1 p.2)
        = (∑ p ∈ Alt,
          (if p.1 = p.2 then (1/2:ℚ) * CFun Tb p.1 p.2 else CFun Tb p.1 p.2) * K p.1 p.2)
          + ∑ p ∈ Aeq, (if p.1 = p.2 then (1/2:ℚ) * CFun Tb p.1 p.2 else CFun Tb p.1 p.2) *
            K p.1 p.2 := by
      rw [hpart, Finset.sum_union hdisj]
    rw [hsplit2]
    have hAltVal : (∑ p ∈ Alt,
          (if p.1 = p.2 then (1/2:ℚ) * CFun Tb p.1 p.2 else CFun Tb p.1 p.2) * K p.1 p.2)
        = ∑ p ∈ Alt, g p.1 p.2 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hAlt, Finset.mem_filter] at hp
      rw [ite_eq_right (fun h => absurd (h ▸ hp.2) (lt_irrefl _)), hg]
    have hAeqVal : (∑ p ∈ Aeq,
          (if p.1 = p.2 then (1/2:ℚ) * CFun Tb p.1 p.2 else CFun Tb p.1 p.2) * K p.1 p.2)
        = (1/2:ℚ) * ∑ i : I n, g i i := by
      have heq : (∑ p ∈ Aeq,
            (if p.1 = p.2 then (1/2:ℚ) * CFun Tb p.1 p.2 else CFun Tb p.1 p.2) * K p.1 p.2)
          = ∑ p ∈ Aeq, (1/2:ℚ) * g p.1 p.2 := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [hAeq, Finset.mem_filter] at hp
        rw [ite_eq_left hp.2, hg]; ring
      rw [heq, Finset.mul_sum]
      apply Finset.sum_nbij' (fun p => p.1) (fun i => (i, i))
      · intro p hp; exact Finset.mem_univ _
      · intro i _
        rw [hAeq, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, rfl⟩
      · intro p hp
        rw [hAeq, Finset.mem_filter] at hp
        exact Prod.ext rfl hp.2
      · intro i _; simp
      · intro p hp
        rw [hAeq, Finset.mem_filter] at hp
        congr 2
        exact hp.2.symm
    rw [hAltVal, hAeqVal]
  rw [hsplit]
  have hfullsym := sym_sum_full_I g hgsym
  have hCF := CFun_full_sum Tb L_block_relation w u
  have hgFull : (∑ i : I n, ∑ j : I n, g i j) = 2 * Tb (Sum.inr w) (Sum.inr u) := by
    rw [hg]; exact hCF
  rw [hgFull] at hfullsym
  linarith [hfullsym]

/-! ## `rho_span`'s even case (`p = 0`) -- assembly

`cEven`'s `L`-part uses `CFun` (off-diagonal pairs) / `(1/2)·CFun` (diagonal, the
`Sof`/`rhoBasis` own missing `1/2`); its `S`-part uses `S_indep_full`'s own extraction
formula (matching `cEven_S_inl_inl`); its `F`-part is `0` (`F`-kind has `parity 1`, so
plays no role for `p = 0`). Unlike `rho_span_odd`, BOTH blocks are matched directly (no
`ospCond`-bootstrap needed), since `cEven_S_inl_inl`/`cEven_L_inr_inr` already give the
`inl`-`inl`/`inr`-`inr` blocks outright; the mixed blocks (`inl`-`inr`, `inr`-`inl`)
vanish on both sides directly (`Homogeneous 0 Tb` on the `Tb` side, `rhoBasis`'s own
kind-vs-input-vs-output support pattern on the `candSum` side, exactly as
`rho_span_odd`'s own `hL`/`hFp`-style arguments used). -/

noncomputable def cEven {F : FermionIndex} {n : ℕ} (Tb : Midx F n → MMod F n) :
    OspBasis F n → ℚ
  | .inl ⟨(u, v), _⟩ => if u = v then (1 / 2 : ℚ) * CFun Tb u v else CFun Tb u v
  | .inr (.inl ⟨(i, j), _⟩) => Tb (Sum.inl (F.dual j)) (Sum.inl i)
  | .inr (.inr _) => 0

theorem cEven_support {F : FermionIndex} {n : ℕ} (Tb : Midx F n → MMod F n) :
    ∀ X : OspBasis F n, parity X ≠ 0 → cEven Tb X = 0 := by
  intro X hX
  match X with
  | .inl ⟨(u, v), _⟩ => exact absurd rfl hX
  | .inr (.inl ⟨(i, j), _⟩) => exact absurd rfl hX
  | .inr (.inr _) => rfl

theorem cEven_inr_inr {F : FermionIndex} {n : ℕ} (Tb : Midx F n → MMod F n)
    (ho : ospCond 0 Tb) (w u : I n) :
    (∑ X : OspBasis F n, cEven Tb X • rhoBasis X (Sum.inr w)) (Sum.inr u)
      = Tb (Sum.inr w) (Sum.inr u) := by
  have goal2 : (∑ X : OspBasis F n, cEven Tb X • rhoBasis X (Sum.inr w)) (Sum.inr u)
      = ∑ X : OspBasis F n, cEven Tb X * rhoBasis X (Sum.inr w) (Sum.inr u) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [goal2]
  have hsplit1 : (∑ X : OspBasis F n, cEven Tb X * rhoBasis X (Sum.inr w) (Sum.inr u))
      = ∑ a : {q : I n × I n // IKey q.1 ≤ IKey q.2},
          cEven Tb (Sum.inl a) * rhoBasis (Sum.inl a : OspBasis F n) (Sum.inr w) (Sum.inr u)
        + ∑ b : ({q : F.K × F.K // F.key q.1 < F.key q.2} ⊕ (I n × F.K)),
          cEven Tb (Sum.inr b) * rhoBasis (Sum.inr b : OspBasis F n) (Sum.inr w) (Sum.inr u) :=
    Fintype.sum_sum_type (fun X => cEven Tb X * rhoBasis X (Sum.inr w) (Sum.inr u))
  rw [hsplit1]
  have hsplit2 : (∑ b : ({q : F.K × F.K // F.key q.1 < F.key q.2} ⊕ (I n × F.K)),
        cEven Tb (Sum.inr b) * rhoBasis (Sum.inr b : OspBasis F n) (Sum.inr w) (Sum.inr u))
      = ∑ Y : {q : F.K × F.K // F.key q.1 < F.key q.2},
          cEven Tb (Sum.inr (Sum.inl Y))
            * rhoBasis (Sum.inr (Sum.inl Y) : OspBasis F n) (Sum.inr w) (Sum.inr u)
        + ∑ Z : I n × F.K,
          cEven Tb (Sum.inr (Sum.inr Z))
            * rhoBasis (Sum.inr (Sum.inr Z) : OspBasis F n) (Sum.inr w) (Sum.inr u) :=
    Fintype.sum_sum_type (fun b =>
      cEven Tb (Sum.inr b) * rhoBasis (Sum.inr b : OspBasis F n) (Sum.inr w) (Sum.inr u))
  rw [hsplit2]
  have hS : ∑ Y : {q : F.K × F.K // F.key q.1 < F.key q.2},
      cEven Tb (Sum.inr (Sum.inl Y)) * rhoBasis (Sum.inr (Sum.inl Y) : OspBasis F n)
        (Sum.inr w) (Sum.inr u) = 0 := by
    apply Finset.sum_eq_zero; intro X _; obtain ⟨⟨i, j⟩, hij⟩ := X
    change cEven Tb (Sum.inr (Sum.inl ⟨(i, j), hij⟩)) *
        (rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) (Sum.inr w) : MMod F n)
          (Sum.inr u) = 0
    simp only [rhoBasis]
    rw [show (0 : MMod F n) (Sum.inr u) = (0:ℚ) from rfl, mul_zero]
  have hFp : ∑ Z : I n × F.K,
      cEven Tb (Sum.inr (Sum.inr Z)) * rhoBasis (Sum.inr (Sum.inr Z) : OspBasis F n)
        (Sum.inr w) (Sum.inr u) = 0 := by
    apply Finset.sum_eq_zero; intro ⟨v, i⟩ _
    change cEven Tb (Sum.inr (Sum.inr (v, i))) *
        (rhoBasis (Sum.inr (Sum.inr (v, i)) : OspBasis F n) (Sum.inr w) : MMod F n) (Sum.inr u) = 0
    simp only [rhoBasis, Pi.smul_apply, smul_eq_mul]
    rw [eNM_inl_inr_eq_zero]; ring
  rw [hS, hFp, zero_add, add_zero]
  have hLconv : (∑ a : {q : I n × I n // IKey q.1 ≤ IKey q.2},
        cEven Tb (Sum.inl a) * rhoBasis (Sum.inl a : OspBasis F n) (Sum.inr w) (Sum.inr u))
      = ∑ p : {q : I n × I n // IKey q.1 ≤ IKey q.2},
          (if p.1.1 = p.1.2 then (1/2 : ℚ) * CFun Tb p.1.1 p.1.2 else CFun Tb p.1.1 p.1.2)
            * ((1/2 : ℚ) * (J n p.1.2 w * (if u = p.1.1 then 1 else 0)
                + J n p.1.1 w * (if u = p.1.2 then 1 else 0))) := by
    apply Finset.sum_congr rfl
    intro p _
    obtain ⟨⟨u0, v0⟩, h⟩ := p
    show cEven Tb (Sum.inl ⟨(u0, v0), h⟩) *
        (rhoBasis (Sum.inl ⟨(u0, v0), h⟩ : OspBasis F n) (Sum.inr w) : MMod F n) (Sum.inr u) = _
    simp only [cEven, rhoBasis, Pi.smul_apply, Pi.add_apply, smul_eq_mul, eNM_I_eq]
  rw [hLconv]
  exact cEven_L_inr_inr Tb (L_block_relation Tb ho) w u

theorem cEven_inl_inl {F : FermionIndex} {n : ℕ} (Tb : Midx F n → MMod F n)
    (ho : ospCond 0 Tb) (a a' : F.K) :
    (∑ X : OspBasis F n, cEven Tb X • rhoBasis X (Sum.inl a)) (Sum.inl a')
      = Tb (Sum.inl a) (Sum.inl a') := by
  have goal2 : (∑ X : OspBasis F n, cEven Tb X • rhoBasis X (Sum.inl a)) (Sum.inl a')
      = ∑ X : OspBasis F n, cEven Tb X * rhoBasis X (Sum.inl a) (Sum.inl a') := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [goal2]
  have hsplit1 : (∑ X : OspBasis F n, cEven Tb X * rhoBasis X (Sum.inl a) (Sum.inl a'))
      = ∑ p : {q : I n × I n // IKey q.1 ≤ IKey q.2},
          cEven Tb (Sum.inl p) * rhoBasis (Sum.inl p : OspBasis F n) (Sum.inl a) (Sum.inl a')
        + ∑ b : ({q : F.K × F.K // F.key q.1 < F.key q.2} ⊕ (I n × F.K)),
          cEven Tb (Sum.inr b) * rhoBasis (Sum.inr b : OspBasis F n) (Sum.inl a) (Sum.inl a') :=
    Fintype.sum_sum_type (fun X => cEven Tb X * rhoBasis X (Sum.inl a) (Sum.inl a'))
  rw [hsplit1]
  have hsplit2 : (∑ b : ({q : F.K × F.K // F.key q.1 < F.key q.2} ⊕ (I n × F.K)),
        cEven Tb (Sum.inr b) * rhoBasis (Sum.inr b : OspBasis F n) (Sum.inl a) (Sum.inl a'))
      = ∑ Y : {q : F.K × F.K // F.key q.1 < F.key q.2},
          cEven Tb (Sum.inr (Sum.inl Y))
            * rhoBasis (Sum.inr (Sum.inl Y) : OspBasis F n) (Sum.inl a) (Sum.inl a')
        + ∑ Z : I n × F.K,
          cEven Tb (Sum.inr (Sum.inr Z))
            * rhoBasis (Sum.inr (Sum.inr Z) : OspBasis F n) (Sum.inl a) (Sum.inl a') :=
    Fintype.sum_sum_type (fun b =>
      cEven Tb (Sum.inr b) * rhoBasis (Sum.inr b : OspBasis F n) (Sum.inl a) (Sum.inl a'))
  rw [hsplit2]
  have hL : ∑ p : {q : I n × I n // IKey q.1 ≤ IKey q.2},
      cEven Tb (Sum.inl p) * rhoBasis (Sum.inl p : OspBasis F n) (Sum.inl a) (Sum.inl a') = 0 := by
    apply Finset.sum_eq_zero; intro X _; obtain ⟨⟨u, v⟩, huv⟩ := X
    change cEven Tb (Sum.inl ⟨(u, v), huv⟩) *
        (rhoBasis (Sum.inl ⟨(u, v), huv⟩ : OspBasis F n) (Sum.inl a) : MMod F n) (Sum.inl a') = 0
    simp only [rhoBasis]
    rw [show (0 : MMod F n) (Sum.inl a') = (0:ℚ) from rfl, mul_zero]
  have hFp : ∑ Z : I n × F.K,
      cEven Tb (Sum.inr (Sum.inr Z)) * rhoBasis (Sum.inr (Sum.inr Z) : OspBasis F n)
        (Sum.inl a) (Sum.inl a') = 0 := by
    apply Finset.sum_eq_zero; intro ⟨v, i⟩ _
    change cEven Tb (Sum.inr (Sum.inr (v, i))) *
        (rhoBasis (Sum.inr (Sum.inr (v, i)) : OspBasis F n) (Sum.inl a) : MMod F n)
          (Sum.inl a') = 0
    simp only [rhoBasis, Pi.smul_apply, smul_eq_mul]
    rw [eNM_inr_inl_eq_zero]; ring
  rw [hL, zero_add, hFp, add_zero]
  have hSconv : (∑ Y : {q : F.K × F.K // F.key q.1 < F.key q.2},
        cEven Tb (Sum.inr (Sum.inl Y)) * rhoBasis (Sum.inr (Sum.inl Y) : OspBasis F n)
          (Sum.inl a) (Sum.inl a'))
      = ∑ p : {q : F.K × F.K // F.key q.1 < F.key q.2},
          (Tb (Sum.inl (F.dual p.1.2)) (Sum.inl p.1.1))
            * (F.g p.1.2 a * (if a' = p.1.1 then (1:ℚ) else 0)
               - F.g p.1.1 a * (if a' = p.1.2 then (1:ℚ) else 0)) := by
    apply Finset.sum_congr rfl
    intro p _
    obtain ⟨⟨i, j⟩, h⟩ := p
    show cEven Tb (Sum.inr (Sum.inl ⟨(i, j), h⟩)) *
        (rhoBasis (Sum.inr (Sum.inl ⟨(i, j), h⟩) : OspBasis F n) (Sum.inl a) : MMod F n)
          (Sum.inl a') = _
    simp only [cEven, rhoBasis, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eNM_K_eq]
  rw [hSconv]
  exact cEven_S_inl_inl Tb ho a a'

/-- **`p = 0`, the surjectivity half of Prop. 3.4's "Bijectivity", the even
case.** Assembles `cEven_inl_inl`/`cEven_inr_inr` (each block matches `Tb` directly)
with the mixed-block vanishing on both sides (`Homogeneous 0 Tb` for `Tb`, `rhoBasis`'s
own kind-support pattern for `candSum`). -/
theorem rho_span_even {F : FermionIndex} {n : ℕ} (Tb : Midx F n → MMod F n)
    (hh : Homogeneous 0 Tb) (ho : ospCond 0 Tb) :
    ∃ c : OspBasis F n → ℚ, (∀ X, parity X ≠ 0 → c X = 0) ∧
      Tb = fun i => ∑ X : OspBasis F n, (c X) • rhoBasis X i := by
  refine ⟨cEven Tb, cEven_support Tb, ?_⟩
  funext i
  match i with
  | .inl a =>
    funext j
    match j with
    | .inl a' => exact (cEven_inl_inl Tb ho a a').symm
    | .inr u =>
      have hz : Tb (Sum.inl a) (Sum.inr u) = 0 := by
        by_contra hzz
        have := hh (Sum.inl a) (Sum.inr u) hzz
        simp only [pM] at this
        exact absurd this (by decide)
      have hz2 : (∑ X : OspBasis F n, cEven Tb X • rhoBasis X (Sum.inl a)) (Sum.inr u) = 0 := by
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_eq_zero
        intro X _
        match X with
        | .inl ⟨(u0, v0), h⟩ =>
          change cEven Tb (Sum.inl ⟨(u0, v0), h⟩) *
              (rhoBasis (Sum.inl ⟨(u0, v0), h⟩ : OspBasis F n) (Sum.inl a) : MMod F n)
                (Sum.inr u) = 0
          simp only [rhoBasis]
          rw [show (0 : MMod F n) (Sum.inr u) = (0:ℚ) from rfl, mul_zero]
        | .inr (.inl ⟨(i0, j0), h⟩) =>
          change cEven Tb (Sum.inr (Sum.inl ⟨(i0, j0), h⟩)) *
              (rhoBasis (Sum.inr (Sum.inl ⟨(i0, j0), h⟩) : OspBasis F n) (Sum.inl a) : MMod F n)
                (Sum.inr u) = 0
          simp only [rhoBasis, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          rw [eNM_inl_inr_eq_zero, eNM_inl_inr_eq_zero]; ring
        | .inr (.inr (v, i0)) => simp [cEven]
      rw [hz, hz2]
  | .inr w =>
    funext j
    match j with
    | .inr u => exact (cEven_inr_inr Tb ho w u).symm
    | .inl a =>
      have hz : Tb (Sum.inr w) (Sum.inl a) = 0 := by
        by_contra hzz
        have := hh (Sum.inr w) (Sum.inl a) hzz
        simp only [pM] at this
        exact absurd this (by decide)
      have hz2 : (∑ X : OspBasis F n, cEven Tb X • rhoBasis X (Sum.inr w)) (Sum.inl a) = 0 := by
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_eq_zero
        intro X _
        match X with
        | .inl ⟨(u0, v0), h⟩ =>
          change cEven Tb (Sum.inl ⟨(u0, v0), h⟩) *
              (rhoBasis (Sum.inl ⟨(u0, v0), h⟩ : OspBasis F n) (Sum.inr w) : MMod F n)
                (Sum.inl a) = 0
          simp only [rhoBasis, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
          rw [eNM_inr_inl_eq_zero, eNM_inr_inl_eq_zero]; ring
        | .inr (.inl ⟨(i0, j0), h⟩) =>
          change cEven Tb (Sum.inr (Sum.inl ⟨(i0, j0), h⟩)) *
              (rhoBasis (Sum.inr (Sum.inl ⟨(i0, j0), h⟩) : OspBasis F n) (Sum.inr w) : MMod F n)
                (Sum.inl a) = 0
          simp only [rhoBasis]
          rw [show (0 : MMod F n) (Sum.inl a) = (0:ℚ) from rfl, mul_zero]
        | .inr (.inr (v, i0)) => simp [cEven]
      rw [hz, hz2]

/-- **`rho_span`, the surjectivity half of bijectivity**: every homogeneous `Tb` of
parity `p` satisfying `ospCond p Tb` is a `ℚ`-combination of the `rhoBasis X` with
`parity X = p`. Together with `rhoBasis_linearIndependent` (injectivity) this gives the
isomorphism `𝔤 ≅ osp(M,𝓑)` of Prop. 3.4. Assembled from `rho_span_odd` (`p = 1`)
and `rho_span_even` (`p = 0`) by cases on `p : ZMod 2` (`fin_cases`, `ZMod 2` being a
2-element `Fintype`). -/
theorem rho_span {F : FermionIndex} {n : ℕ} (p : ZMod 2) (Tb : Midx F n → MMod F n)
    (hh : Homogeneous p Tb) (ho : ospCond p Tb) :
    ∃ c : OspBasis F n → ℚ, (∀ X, parity X ≠ p → c X = 0) ∧
      Tb = fun i => ∑ X : OspBasis F n, (c X) • rhoBasis X i := by
  fin_cases p
  · exact rho_span_even Tb hh ho
  · exact rho_span_odd Tb hh ho

/-! ## `rho_bracket`'s own toolkit

A direct computation (rather than a route through the associativity of `AB F n`, which would
need a bridge from `rhoBasis`/`rhoOp` to `AB`/`X0`/`iota0`): split into `OspBasis F n`'s own
9 kind pairs against `bracket0Basis`'s own 9-way match, mirroring `OspN/Coboundary.lean`'s
`Gamma_eq_delta_hTilde_basis` (a structurally identical 9-sector proof for a different
identity). `rho_bracket_reversal` below (from `bracket0Basis_super_skew`)
lets 3 of the 9 sectors (`S,L` / `F,L` / `F,S`) be derived directly from their own
reverse (`L,S` / `L,F` / `S,F`) rather than reproved from scratch -- so only 6 sectors
need genuine work: `L,L`, `L,S` (trivial, `bracket0Basis=0`), `L,F`, `S,S`,
`S,F`, `F,F`. -/

theorem bracket0BasisQ_antisymm {F : FermionIndex} {n : ℕ} (X Y : OspBasis F n)
    (k : OspBasis F n) :
    bracket0BasisQ X Y k = -(gsign (parity X) (parity Y)) * bracket0BasisQ Y X k := by
  unfold bracket0BasisQ
  rw [bracket0Basis_super_skew X Y]
  simp only [Pi.smul_apply]
  rw [Algebra.smul_def, map_mul]
  simp

/-- If `rho_bracket`'s own identity holds for `(X,Y,i)`, it holds for `(Y,X,i)` too --
from `gsign`'s own symmetry, `gsign p q * gsign p q = 1` (`gsign_sq`, already proved),
and `bracket0BasisQ_antisymm`. Halves the sector work: only 6 of the 9 kind pairs need
a genuine proof. -/
theorem rho_bracket_reversal {F : FermionIndex} {n : ℕ} (X Y : OspBasis F n) (i : Midx F n)
    (h : rhoOp X (rhoBasis Y i) - gsign (parity X) (parity Y) • rhoOp Y (rhoBasis X i)
      = ∑ k : OspBasis F n, (bracket0BasisQ X Y k) • rhoBasis k i) :
    rhoOp Y (rhoBasis X i) - gsign (parity Y) (parity X) • rhoOp X (rhoBasis Y i)
      = ∑ k : OspBasis F n, (bracket0BasisQ Y X k) • rhoBasis k i := by
  have hgsymm : gsign (parity Y) (parity X) = gsign (parity X) (parity Y) := by
    unfold gsign; by_cases h1 : parity X = 1 <;> by_cases h2 : parity Y = 1 <;> simp_all
  rw [hgsymm]
  set g := gsign (parity X) (parity Y) with hg
  have hgg : g * g = 1 := by rw [hg]; exact gsign_sq _ _
  have key : rhoOp Y (rhoBasis X i) - g • rhoOp X (rhoBasis Y i)
      = (-g) • (rhoOp X (rhoBasis Y i) - g • rhoOp Y (rhoBasis X i)) := by
    rw [smul_sub, smul_smul]
    rw [show -g * g = -(g*g) from by ring, hgg]
    funext j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [key, h]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [smul_smul, bracket0BasisQ_antisymm Y X k, hgsymm]

theorem Lof_ne_inr {F : FermionIndex} {n : ℕ} (a b : I n)
    (x : {q : F.K × F.K // F.key q.1 < F.key q.2} ⊕ (I n × F.K)) :
    (Lof a b : OspBasis F n) ≠ Sum.inr x := by
  unfold Lof; split_ifs <;> simp

theorem rhoBasis_Lof {F : FermionIndex} {n : ℕ} (u v w : I n) :
    (rhoBasis (Lof u v : OspBasis F n) (Sum.inr w) : MMod F n)
      = (1/2 : ℚ) • (J n v w • eNM (Sum.inr u) + J n u w • eNM (Sum.inr v)) := by
  unfold Lof
  split_ifs with h
  · rfl
  · change (rhoBasis (Sum.inl ⟨(v, u), (Nat.not_le.mp h).le⟩ : OspBasis F n) (Sum.inr w) : MMod F n)
        = _
    unfold rhoBasis
    funext x
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring

theorem bracket0BasisQ_Lof_Lof {F : FermionIndex} {n : ℕ} (u v w z : I n) (k : OspBasis F n) :
    bracket0BasisQ (Lof u v : OspBasis F n) (Lof w z : OspBasis F n) k
      = (1/2 * J n v w) * (if k = Lof u z then (1:ℚ) else 0)
        + (1/2 * J n u w) * (if k = Lof v z then (1:ℚ) else 0)
        + (1/2 * J n v z) * (if k = Lof u w then (1:ℚ) else 0)
        + (1/2 * J n u z) * (if k = Lof v w then (1:ℚ) else 0) := by
  unfold bracket0BasisQ
  have heq : (bracket0Basis (Lof u v : OspBasis F n) (Lof w z : OspBasis F n) : OspMod F n)
      = bracketLL u v w z := by
    unfold Lof
    split_ifs with h1 h2 <;> unfold bracket0Basis bracketLL <;> funext k' <;>
      simp only [Pi.add_apply, Pi.smul_apply] <;> ring
  rw [show bracket0Basis (Lof u v : OspBasis F n) (Lof w z : OspBasis F n) k
      = bracketLL u v w z k from by rw [heq]]
  unfold bracketLL
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [eN_eq_algebraMap, eN_eq_algebraMap, eN_eq_algebraMap, eN_eq_algebraMap]
  simp only [Algebra.algebraMap_eq_smul_one, smul_smul]
  split_ifs <;> simp

theorem rhoOp_Lof_Lof_inr {F : FermionIndex} {n : ℕ} (a b c d t s : I n) :
    rhoOp (Lof a b : OspBasis F n) (rhoBasis (Lof c d : OspBasis F n) (Sum.inr t)) (Sum.inr s)
      = (1/4 : ℚ) * (J n d t * J n b c * (if s = a then 1 else 0)
          + J n d t * J n a c * (if s = b then 1 else 0)
          + J n c t * J n b d * (if s = a then 1 else 0)
          + J n c t * J n a d * (if s = b then 1 else 0)) := by
  unfold rhoOp
  have hsplit : (∑ l : Midx F n, (rhoBasis (Lof c d : OspBasis F n) (Sum.inr t) : MMod F n) l
        * rhoBasis (Lof a b : OspBasis F n) l (Sum.inr s))
      = ∑ a' : F.K, (rhoBasis (Lof c d : OspBasis F n) (Sum.inr t) : MMod F n) (Sum.inl a')
          * rhoBasis (Lof a b : OspBasis F n) (Sum.inl a') (Sum.inr s)
        + ∑ l : I n, (rhoBasis (Lof c d : OspBasis F n) (Sum.inr t) : MMod F n) (Sum.inr l)
          * rhoBasis (Lof a b : OspBasis F n) (Sum.inr l) (Sum.inr s) :=
    Fintype.sum_sum_type (fun l => (rhoBasis (Lof c d : OspBasis F n) (Sum.inr t) : MMod F n) l
      * rhoBasis (Lof a b : OspBasis F n) l (Sum.inr s))
  rw [hsplit]
  have hz : (∑ a' : F.K, (rhoBasis (Lof c d : OspBasis F n) (Sum.inr t) : MMod F n) (Sum.inl a')
        * rhoBasis (Lof a b : OspBasis F n) (Sum.inl a') (Sum.inr s)) = 0 := by
    apply Finset.sum_eq_zero; intro l _
    rw [rhoBasis_Lof]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have h1 : (eNM (Sum.inr c) : MMod F n) (Sum.inl l) = 0 := by unfold eNM; simp
    have h2 : (eNM (Sum.inr d) : MMod F n) (Sum.inl l) = 0 := by unfold eNM; simp
    rw [h1, h2]; ring
  rw [hz, zero_add]
  have hexp : (∑ l : I n, (rhoBasis (Lof c d : OspBasis F n) (Sum.inr t) : MMod F n) (Sum.inr l)
        * rhoBasis (Lof a b : OspBasis F n) (Sum.inr l) (Sum.inr s))
      = ∑ l : I n, ((1/2:ℚ) * (J n d t * (if l = c then 1 else 0)
          + J n c t * (if l = d then 1 else 0)))
          * rhoBasis (Lof a b : OspBasis F n) (Sum.inr l) (Sum.inr s) := by
    apply Finset.sum_congr rfl; intro l _
    rw [rhoBasis_Lof]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, eNM_I_eq]
  rw [hexp]
  have hfac : (∑ l : I n, ((1/2:ℚ) * (J n d t * (if l = c then 1 else 0)
        + J n c t * (if l = d then 1 else 0)))
        * rhoBasis (Lof a b : OspBasis F n) (Sum.inr l) (Sum.inr s))
      = (1/2:ℚ) * J n d t * ∑ l : I n, (if l = c then (1:ℚ) else 0)
          * rhoBasis (Lof a b : OspBasis F n) (Sum.inr l) (Sum.inr s)
        + (1/2:ℚ) * J n c t * ∑ l : I n, (if l = d then (1:ℚ) else 0)
          * rhoBasis (Lof a b : OspBasis F n) (Sum.inr l) (Sum.inr s) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro l _; ring
  rw [hfac]
  have hc1 : (∑ l : I n, (if l = c then (1:ℚ) else 0)
        * rhoBasis (Lof a b : OspBasis F n) (Sum.inr l) (Sum.inr s))
      = rhoBasis (Lof a b : OspBasis F n) (Sum.inr c) (Sum.inr s) := by
    rw [Finset.sum_eq_single c]
    · simp
    · intro l _ hl; simp [hl]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hc2 : (∑ l : I n, (if l = d then (1:ℚ) else 0)
        * rhoBasis (Lof a b : OspBasis F n) (Sum.inr l) (Sum.inr s))
      = rhoBasis (Lof a b : OspBasis F n) (Sum.inr d) (Sum.inr s) := by
    rw [Finset.sum_eq_single d]
    · simp
    · intro l _ hl; simp [hl]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hc1, hc2, rhoBasis_Lof, rhoBasis_Lof]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, eNM_I_eq]
  ring

theorem rho_bracket_LL_inl {F : FermionIndex} {n : ℕ} (u v w z : I n) (a : F.K) :
    (rhoOp (Lof u v : OspBasis F n) (rhoBasis (Lof w z : OspBasis F n) (Sum.inl a))
        - gsign (parity (Lof u v : OspBasis F n)) (parity (Lof w z : OspBasis F n))
          • rhoOp (Lof w z : OspBasis F n) (rhoBasis (Lof u v : OspBasis F n) (Sum.inl a)))
      = ∑ k : OspBasis F n, (bracket0BasisQ (Lof u v : OspBasis F n) (Lof w z : OspBasis F n) k)
          • rhoBasis k (Sum.inl a) := by
  have hL1 : (rhoBasis (Lof w z : OspBasis F n) (Sum.inl a) : MMod F n) = 0 := by
    unfold Lof; split_ifs <;> unfold rhoBasis <;> rfl
  have hL2 : (rhoBasis (Lof u v : OspBasis F n) (Sum.inl a) : MMod F n) = 0 := by
    unfold Lof; split_ifs <;> unfold rhoBasis <;> rfl
  rw [hL1, hL2]
  have hop1 : rhoOp (Lof u v : OspBasis F n) (0 : MMod F n) = 0 := by unfold rhoOp; funext j; simp
  have hop2 : rhoOp (Lof w z : OspBasis F n) (0 : MMod F n) = 0 := by unfold rhoOp; funext j; simp
  rw [hop1, hop2, smul_zero, sub_zero]
  symm
  apply Finset.sum_eq_zero
  intro k _
  match k with
  | .inl ⟨(p, q), h⟩ =>
    have hz : (rhoBasis (Sum.inl ⟨(p, q), h⟩ : OspBasis F n) (Sum.inl a) : MMod F n) = 0 := rfl
    rw [hz]; simp
  | .inr (.inl ⟨(i0, j0), h⟩) =>
    have hq : bracket0BasisQ (Lof u v : OspBasis F n) (Lof w z : OspBasis F n)
        (Sum.inr (Sum.inl ⟨(i0, j0), h⟩)) = 0 := by
      rw [bracket0BasisQ_Lof_Lof]
      simp [Ne.symm (Lof_ne_inr u z (Sum.inl ⟨(i0, j0), h⟩)),
        Ne.symm (Lof_ne_inr v z (Sum.inl ⟨(i0, j0), h⟩)),
        Ne.symm (Lof_ne_inr u w (Sum.inl ⟨(i0, j0), h⟩)),
        Ne.symm (Lof_ne_inr v w (Sum.inl ⟨(i0, j0), h⟩))]
    rw [hq]; simp
  | .inr (.inr (u0, i0)) =>
    have hq : bracket0BasisQ (Lof u v : OspBasis F n) (Lof w z : OspBasis F n)
        (Sum.inr (Sum.inr (u0, i0))) = 0 := by
      rw [bracket0BasisQ_Lof_Lof]
      simp [Ne.symm (Lof_ne_inr u z (Sum.inr (u0, i0))), Ne.symm
        (Lof_ne_inr v z (Sum.inr (u0, i0))),
        Ne.symm (Lof_ne_inr u w (Sum.inr (u0, i0))), Ne.symm (Lof_ne_inr v w (Sum.inr (u0, i0)))]
    rw [hq]; simp

theorem rho_bracket_LL_inr {F : FermionIndex} {n : ℕ} (u v w z t s : I n) :
    (rhoOp (Lof u v : OspBasis F n) (rhoBasis (Lof w z : OspBasis F n) (Sum.inr t))
        - gsign (parity (Lof u v : OspBasis F n)) (parity (Lof w z : OspBasis F n))
          • rhoOp (Lof w z : OspBasis F n) (rhoBasis (Lof u v : OspBasis F n) (Sum.inr t)))
        (Sum.inr s)
      = ∑ k : OspBasis F n, (bracket0BasisQ (Lof u v : OspBasis F n) (Lof w z : OspBasis F n) k)
          • rhoBasis k (Sum.inr t) (Sum.inr s) := by
  have hpar : parity (Lof u v : OspBasis F n) = 0 := by unfold Lof; split_ifs <;> rfl
  have hpar2 : parity (Lof w z : OspBasis F n) = 0 := by unfold Lof; split_ifs <;> rfl
  rw [hpar, hpar2, gsign_zero_left, one_smul]
  simp only [Pi.sub_apply]
  rw [rhoOp_Lof_Lof_inr, rhoOp_Lof_Lof_inr]
  have hrhs : (∑ k : OspBasis F n,
        (bracket0BasisQ (Lof u v : OspBasis F n) (Lof w z : OspBasis F n) k)
          • rhoBasis k (Sum.inr t) (Sum.inr s))
      = (1/2 * J n v w) * rhoBasis (Lof u z : OspBasis F n) (Sum.inr t) (Sum.inr s)
        + (1/2 * J n u w) * rhoBasis (Lof v z : OspBasis F n) (Sum.inr t) (Sum.inr s)
        + (1/2 * J n v z) * rhoBasis (Lof u w : OspBasis F n) (Sum.inr t) (Sum.inr s)
        + (1/2 * J n u z) * rhoBasis (Lof v w : OspBasis F n) (Sum.inr t) (Sum.inr s) := by
    have heq : (∑ k : OspBasis F n,
          bracket0BasisQ (Lof u v : OspBasis F n) (Lof w z : OspBasis F n) k
            • rhoBasis k (Sum.inr t) (Sum.inr s))
        = ∑ k : OspBasis F n, ((1/2 * J n v w) * (if k = Lof u z then (1:ℚ) else 0)
            + (1/2 * J n u w) * (if k = Lof v z then (1:ℚ) else 0)
            + (1/2 * J n v z) * (if k = Lof u w then (1:ℚ) else 0)
            + (1/2 * J n u z) * (if k = Lof v w then (1:ℚ) else 0))
            * rhoBasis k (Sum.inr t) (Sum.inr s) := by
      apply Finset.sum_congr rfl; intro k _
      rw [bracket0BasisQ_Lof_Lof, smul_eq_mul]
    rw [heq]
    rw [show (∑ k : OspBasis F n, ((1/2 * J n v w) * (if k = Lof u z then (1:ℚ) else 0)
            + (1/2 * J n u w) * (if k = Lof v z then (1:ℚ) else 0)
            + (1/2 * J n v z) * (if k = Lof u w then (1:ℚ) else 0)
            + (1/2 * J n u z) * (if k = Lof v w then (1:ℚ) else 0))
            * rhoBasis k (Sum.inr t) (Sum.inr s))
        = (∑ k : OspBasis F n, (1/2 * J n v w) * (if k = Lof u z then (1:ℚ) else 0)
              * rhoBasis k (Sum.inr t) (Sum.inr s))
          + (∑ k : OspBasis F n, (1/2 * J n u w) * (if k = Lof v z then (1:ℚ) else 0)
              * rhoBasis k (Sum.inr t) (Sum.inr s))
          + (∑ k : OspBasis F n, (1/2 * J n v z) * (if k = Lof u w then (1:ℚ) else 0)
              * rhoBasis k (Sum.inr t) (Sum.inr s))
          + (∑ k : OspBasis F n, (1/2 * J n u z) * (if k = Lof v w then (1:ℚ) else 0)
              * rhoBasis k (Sum.inr t) (Sum.inr s))
        from by rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl; intro k _; ring]
    refine congrArg₂ _ (congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_) ?_
    · rw [Finset.sum_eq_single (Lof u z : OspBasis F n)]
      · simp
      · intro k _ hk; simp [hk]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_single (Lof v z : OspBasis F n)]
      · simp
      · intro k _ hk; simp [hk]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_single (Lof u w : OspBasis F n)]
      · simp
      · intro k _ hk; simp [hk]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_single (Lof v w : OspBasis F n)]
      · simp
      · intro k _ hk; simp [hk]
      · intro h; exact absurd (Finset.mem_univ _) h
  rw [hrhs, rhoBasis_Lof, rhoBasis_Lof, rhoBasis_Lof, rhoBasis_Lof]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, eNM_I_eq]
  rw [J_antisymm z u, J_antisymm w u, J_antisymm z v, J_antisymm w v]
  ring

/-- The `L,L` sector at `i = inr t`, read off at output component `s = inl a`: both
sides `0` outright, since `L`-kind's own `rhoBasis` (in either the outer `i`-slot or
the inner sum defining `rhoOp`) has support only on `inr`-type output, and
`bracket0BasisQ` restricted to non-`Lof` basis elements is `0` (`Lof_ne_inr`). -/
theorem rho_bracket_LL_inr_inl {F : FermionIndex} {n : ℕ} (u v w z t : I n) (a : F.K) :
    (rhoOp (Lof u v : OspBasis F n) (rhoBasis (Lof w z : OspBasis F n) (Sum.inr t))
        - gsign (parity (Lof u v : OspBasis F n)) (parity (Lof w z : OspBasis F n))
          • rhoOp (Lof w z : OspBasis F n) (rhoBasis (Lof u v : OspBasis F n) (Sum.inr t)))
        (Sum.inl a)
      = ∑ k : OspBasis F n, (bracket0BasisQ (Lof u v : OspBasis F n) (Lof w z : OspBasis F n) k)
          • rhoBasis k (Sum.inr t) (Sum.inl a) := by
  have hrho0 : ∀ (p q : I n) (l : Midx F n), (rhoBasis (Lof p q : OspBasis F n) l : MMod F n)
      (Sum.inl a) = 0 := by
    intro p q l
    match l with
    | .inl _ => unfold Lof; split_ifs <;> unfold rhoBasis <;> rfl
    | .inr _ =>
      unfold Lof; split_ifs <;> unfold rhoBasis <;>
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] <;>
        rw [show (eNM (Sum.inr p) : MMod F n) (Sum.inl a) = 0 from by unfold eNM; simp,
          show (eNM (Sum.inr q) : MMod F n) (Sum.inl a) = 0 from by unfold eNM; simp] <;> ring
  have hrho0' : ∀ (p q : I n) (h : IKey p ≤ IKey q),
      (rhoBasis (Sum.inl ⟨(p, q), h⟩ : OspBasis F n) (Sum.inr t) : MMod F n) (Sum.inl a) = 0 := by
    intro p q h
    unfold rhoBasis
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [show (eNM (Sum.inr p) : MMod F n) (Sum.inl a) = 0 from by unfold eNM; simp,
      show (eNM (Sum.inr q) : MMod F n) (Sum.inl a) = 0 from by unfold eNM; simp]
    ring
  have hop1 : (rhoOp (Lof u v : OspBasis F n) (rhoBasis (Lof w z : OspBasis F n) (Sum.inr t)))
      (Sum.inl a) = 0 := by
    unfold rhoOp; apply Finset.sum_eq_zero; intro l _; rw [hrho0 u v l]; ring
  have hop2 : (rhoOp (Lof w z : OspBasis F n) (rhoBasis (Lof u v : OspBasis F n) (Sum.inr t)))
      (Sum.inl a) = 0 := by
    unfold rhoOp; apply Finset.sum_eq_zero; intro l _; rw [hrho0 w z l]; ring
  rw [show (rhoOp (Lof u v : OspBasis F n) (rhoBasis (Lof w z : OspBasis F n) (Sum.inr t))
        - gsign (parity (Lof u v : OspBasis F n)) (parity (Lof w z : OspBasis F n))
          • rhoOp (Lof w z : OspBasis F n) (rhoBasis (Lof u v : OspBasis F n) (Sum.inr t)))
        (Sum.inl a)
      = (rhoOp (Lof u v : OspBasis F n) (rhoBasis (Lof w z : OspBasis F n) (Sum.inr t))) (Sum.inl a)
        - gsign (parity (Lof u v : OspBasis F n)) (parity (Lof w z : OspBasis F n))
          * (rhoOp (Lof w z : OspBasis F n) (rhoBasis (Lof u v : OspBasis F n) (Sum.inr t)))
            (Sum.inl a) from rfl]
  rw [hop1, hop2]; ring_nf
  symm
  apply Finset.sum_eq_zero
  intro k _
  match k with
  | .inl ⟨(p, q), h⟩ => rw [hrho0' p q h]; simp
  | .inr (.inl ⟨(i0, j0), h⟩) =>
    have hq : bracket0BasisQ (Lof u v : OspBasis F n) (Lof w z : OspBasis F n)
        (Sum.inr (Sum.inl ⟨(i0, j0), h⟩)) = 0 := by
      rw [bracket0BasisQ_Lof_Lof]
      simp [Ne.symm (Lof_ne_inr u z (Sum.inl ⟨(i0, j0), h⟩)),
        Ne.symm (Lof_ne_inr v z (Sum.inl ⟨(i0, j0), h⟩)),
        Ne.symm (Lof_ne_inr u w (Sum.inl ⟨(i0, j0), h⟩)),
        Ne.symm (Lof_ne_inr v w (Sum.inl ⟨(i0, j0), h⟩))]
    rw [hq]; simp
  | .inr (.inr (u0, i0)) =>
    have hq : bracket0BasisQ (Lof u v : OspBasis F n) (Lof w z : OspBasis F n)
        (Sum.inr (Sum.inr (u0, i0))) = 0 := by
      rw [bracket0BasisQ_Lof_Lof]
      simp [Ne.symm (Lof_ne_inr u z (Sum.inr (u0, i0))), Ne.symm
        (Lof_ne_inr v z (Sum.inr (u0, i0))),
        Ne.symm (Lof_ne_inr u w (Sum.inr (u0, i0))), Ne.symm (Lof_ne_inr v w (Sum.inr (u0, i0)))]
    rw [hq]; simp

/-- **The `L,L` sector of `rho_bracket`**, for arbitrary `i : Midx F n`: `rho_bracket_LL_inl`
handles `i = inl a` (both sides `0` outright, `L`-kind's own support pattern);
`rho_bracket_LL_inr` handles `i = inr t, s = inr s'` (the genuine computation,
`J_antisymm` closing the final algebra); `rho_bracket_LL_inr_inl` handles `i = inr t, s
= inl a` (both sides `0` again, the "wrong output kind" case). -/
theorem rho_bracket_LL {F : FermionIndex} {n : ℕ} (u v w z : I n) (i : Midx F n) :
    rhoOp (Lof u v : OspBasis F n) (rhoBasis (Lof w z : OspBasis F n) i)
        - gsign (parity (Lof u v : OspBasis F n)) (parity (Lof w z : OspBasis F n))
          • rhoOp (Lof w z : OspBasis F n) (rhoBasis (Lof u v : OspBasis F n) i)
      = ∑ k : OspBasis F n, (bracket0BasisQ (Lof u v : OspBasis F n) (Lof w z : OspBasis F n) k)
          • rhoBasis k i := by
  match i with
  | .inl a => exact rho_bracket_LL_inl u v w z a
  | .inr t =>
    funext s
    simp only [Finset.sum_apply, Pi.smul_apply]
    match s with
    | .inr s' => exact rho_bracket_LL_inr u v w z t s'
    | .inl a => exact rho_bracket_LL_inr_inl u v w z t a

/-- **The `L,S` sector of `rho_bracket`** — trivial: `bracket0Basis` is literally `0`
for an `(L,S)` kind pair, and `L`-kind's own `rhoBasis` is supported only on the
`inr`-`inr` block while `S`-kind's is supported only on the `inl`-`inl` block, so both
`rhoOp` compositions vanish identically for any `i`. The cross-support vanishing uses
`eNM_inl_inr_eq_zero`/`eNM_inr_inl_eq_zero`. -/
theorem rho_bracket_LS {F : FermionIndex} {n : ℕ} (u v : I n) (huv : IKey u ≤ IKey v)
    (i0 j0 : F.K) (hij : F.key i0 < F.key j0) (i : Midx F n) :
    rhoOp (Sum.inl ⟨(u, v), huv⟩ : OspBasis F n) (rhoBasis (Sum.inr (Sum.inl ⟨(i0, j0), hij⟩)) i)
        - gsign (parity (Sum.inl ⟨(u, v), huv⟩ : OspBasis F n))
            (parity (Sum.inr (Sum.inl ⟨(i0, j0), hij⟩) : OspBasis F n))
          • rhoOp (Sum.inr (Sum.inl ⟨(i0, j0), hij⟩) : OspBasis F n)
              (rhoBasis (Sum.inl ⟨(u, v), huv⟩ : OspBasis F n) i)
      = ∑ k : OspBasis F n,
          (bracket0BasisQ (Sum.inl ⟨(u, v), huv⟩ : OspBasis F n)
              (Sum.inr (Sum.inl ⟨(i0, j0), hij⟩)) k) • rhoBasis k i := by
  have hbq : bracket0BasisQ (Sum.inl ⟨(u, v), huv⟩ : OspBasis F n)
      (Sum.inr (Sum.inl ⟨(i0, j0), hij⟩) : OspBasis F n) = 0 := by
    funext k
    unfold bracket0BasisQ bracket0Basis
    simp
  rw [hbq]
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  have hop1 : rhoOp (Sum.inl ⟨(u, v), huv⟩ : OspBasis F n)
      (rhoBasis (Sum.inr (Sum.inl ⟨(i0, j0), hij⟩)) i) = 0 := by
    unfold rhoOp; funext j; apply Finset.sum_eq_zero; intro l _
    match l with
    | .inl a =>
      have h1 : (rhoBasis (Sum.inl ⟨(u, v), huv⟩ : OspBasis F n) (Sum.inl a) : MMod F n) j = 0 := by
        unfold rhoBasis; rfl
      simp [h1]
    | .inr b =>
      have h1 : (rhoBasis (Sum.inr (Sum.inl ⟨(i0, j0), hij⟩) : OspBasis F n) i : MMod F n)
          (Sum.inr b) = 0 := by
        match i with
        | .inl a =>
          unfold rhoBasis
          simp [eNM_inl_inr_eq_zero]
        | .inr t => unfold rhoBasis; rfl
      simp [h1]
  have hop2 : rhoOp (Sum.inr (Sum.inl ⟨(i0, j0), hij⟩) : OspBasis F n)
      (rhoBasis (Sum.inl ⟨(u, v), huv⟩ : OspBasis F n) i) = 0 := by
    unfold rhoOp; funext j; apply Finset.sum_eq_zero; intro l _
    match l with
    | .inr b =>
      have h1 : (rhoBasis (Sum.inr (Sum.inl ⟨(i0, j0), hij⟩) : OspBasis F n) (Sum.inr b)
          : MMod F n) j = 0 := by unfold rhoBasis; rfl
      simp [h1]
    | .inl a =>
      have h1 : (rhoBasis (Sum.inl ⟨(u, v), huv⟩ : OspBasis F n) i : MMod F n) (Sum.inl a) = 0 := by
        match i with
        | .inl b => unfold rhoBasis; rfl
        | .inr t =>
          unfold rhoBasis
          simp [eNM_inr_inl_eq_zero]
      simp [h1]
  rw [hop1, hop2, smul_zero, sub_zero]

theorem rhoBasis_Fof_inl {F : FermionIndex} {n : ℕ} (w : I n) (j0 : F.K) (a : F.K) :
    (rhoBasis (Fof w j0 : OspBasis F n) (Sum.inl a) : MMod F n)
      = (1/2 : ℚ) • (F.g j0 a • eNM (Sum.inr w)) := by
  unfold Fof rhoBasis; rfl

theorem rhoBasis_Fof_inr {F : FermionIndex} {n : ℕ} (w : I n) (j0 : F.K) (t : I n) :
    (rhoBasis (Fof w j0 : OspBasis F n) (Sum.inr t) : MMod F n)
      = (1/2 : ℚ) • (J n w t • eNM (Sum.inl j0)) := by
  unfold Fof rhoBasis; rfl

theorem rhoBasis_Lof_inl_eq_zero {F : FermionIndex} {n : ℕ} (p q : I n) (l : Midx F n) (a : F.K) :
    (rhoBasis (Lof p q : OspBasis F n) l : MMod F n) (Sum.inl a) = 0 := by
  match l with
  | .inl _ => unfold Lof; split_ifs <;> unfold rhoBasis <;> rfl
  | .inr _ =>
    unfold Lof; split_ifs <;> unfold rhoBasis <;>
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] <;>
      rw [show (eNM (Sum.inr p) : MMod F n) (Sum.inl a) = 0 from by unfold eNM; simp,
        show (eNM (Sum.inr q) : MMod F n) (Sum.inl a) = 0 from by unfold eNM; simp] <;> ring

theorem bracket0BasisQ_Lof_Fof {F : FermionIndex} {n : ℕ} (u v w0 : I n) (j0 : F.K)
    (k : OspBasis F n) :
    bracket0BasisQ (Lof u v : OspBasis F n) (Fof w0 j0 : OspBasis F n) k
      = (1/2 * J n v w0) * (if k = Fof u j0 then (1:ℚ) else 0)
        + (1/2 * J n u w0) * (if k = Fof v j0 then (1:ℚ) else 0) := by
  unfold bracket0BasisQ
  have heq : (bracket0Basis (Lof u v : OspBasis F n) (Fof w0 j0 : OspBasis F n) : OspMod F n)
      = bracketLF u v w0 j0 := by
    unfold Lof Fof
    split_ifs with h <;> (unfold bracket0Basis bracketLF; funext k') <;>
      simp only [Pi.add_apply, Pi.smul_apply]
    all_goals ring
  rw [show bracket0Basis (Lof u v : OspBasis F n) (Fof w0 j0 : OspBasis F n) k
      = bracketLF u v w0 j0 k from by rw [heq]]
  unfold bracketLF
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [eN_eq_algebraMap, eN_eq_algebraMap]
  simp only [Algebra.algebraMap_eq_smul_one, smul_smul]
  split_ifs <;> simp

theorem rhoOp_Lof_Fof_inl_inr {F : FermionIndex} {n : ℕ} (u v w0 : I n) (j0 a : F.K) (s : I n) :
    rhoOp (Lof u v : OspBasis F n) (rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inl a)) (Sum.inr s)
      = (1/4 : ℚ) * F.g j0 a * (J n v w0 * (if s = u then 1 else 0)
          + J n u w0 * (if s = v then 1 else 0)) := by
  unfold rhoOp
  have hsplit : (∑ l : Midx F n,
        (rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inl a) : MMod F n) l
        * rhoBasis (Lof u v : OspBasis F n) l (Sum.inr s))
      = ∑ k : F.K, (rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inl a) : MMod F n) (Sum.inl k)
          * rhoBasis (Lof u v : OspBasis F n) (Sum.inl k) (Sum.inr s)
        + ∑ l : I n, (rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inl a) : MMod F n) (Sum.inr l)
          * rhoBasis (Lof u v : OspBasis F n) (Sum.inr l) (Sum.inr s) :=
    Fintype.sum_sum_type (fun l => (rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inl a) : MMod F n) l
      * rhoBasis (Lof u v : OspBasis F n) l (Sum.inr s))
  rw [hsplit]
  have hz1 : (∑ k : F.K, (rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inl a) : MMod F n) (Sum.inl k)
        * rhoBasis (Lof u v : OspBasis F n) (Sum.inl k) (Sum.inr s)) = 0 := by
    apply Finset.sum_eq_zero; intro k _
    have h1 : (rhoBasis (Lof u v : OspBasis F n) (Sum.inl k) : MMod F n) = 0 := by
      unfold Lof; split_ifs <;> unfold rhoBasis <;> rfl
    rw [h1, show (0 : MMod F n) (Sum.inr s) = (0:ℚ) from rfl, mul_zero]
  rw [hz1, zero_add]
  have hexp : (∑ l : I n, (rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inl a) : MMod F n) (Sum.inr l)
        * rhoBasis (Lof u v : OspBasis F n) (Sum.inr l) (Sum.inr s))
      = ∑ l : I n, ((1/2 : ℚ) * F.g j0 a * (if l = w0 then (1:ℚ) else 0))
          * rhoBasis (Lof u v : OspBasis F n) (Sum.inr l) (Sum.inr s) := by
    apply Finset.sum_congr rfl; intro l _
    rw [rhoBasis_Fof_inl]
    simp only [Pi.smul_apply, smul_eq_mul, eNM_I_eq]
    split_ifs <;> ring
  rw [hexp]
  have hfac : (∑ l : I n, ((1/2 : ℚ) * F.g j0 a * (if l = w0 then (1:ℚ) else 0))
        * rhoBasis (Lof u v : OspBasis F n) (Sum.inr l) (Sum.inr s))
      = (1/2 : ℚ) * F.g j0 a * ∑ l : I n, (if l = w0 then (1:ℚ) else 0)
          * rhoBasis (Lof u v : OspBasis F n) (Sum.inr l) (Sum.inr s) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; split_ifs <;> ring
  rw [hfac]
  have hc : (∑ l : I n, (if l = w0 then (1:ℚ) else 0)
        * rhoBasis (Lof u v : OspBasis F n) (Sum.inr l) (Sum.inr s))
      = rhoBasis (Lof u v : OspBasis F n) (Sum.inr w0) (Sum.inr s) := by
    rw [Finset.sum_eq_single w0]
    · simp
    · intro l _ hl; simp [hl]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hc, rhoBasis_Lof]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, eNM_I_eq]
  ring

theorem rhoOp_Lof_Fof_inl_inl {F : FermionIndex} {n : ℕ} (u v w0 : I n) (j0 a : F.K) (a' : F.K) :
    rhoOp (Lof u v : OspBasis F n) (rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inl a)) (Sum.inl a')
      = 0 := by
  unfold rhoOp; apply Finset.sum_eq_zero; intro l _
  rw [rhoBasis_Lof_inl_eq_zero u v l a']; ring

theorem rhoOp_Lof_Fof_inr_zero {F : FermionIndex} {n : ℕ} (u v w0 : I n) (j0 : F.K) (t0 : I n) :
    rhoOp (Lof u v : OspBasis F n) (rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inr t0)) = 0 := by
  unfold rhoOp; funext j
  apply Finset.sum_eq_zero; intro l _
  match l with
  | .inl k =>
    have h1 : (rhoBasis (Lof u v : OspBasis F n) (Sum.inl k) : MMod F n) = 0 := by
      unfold Lof; split_ifs <;> unfold rhoBasis <;> rfl
    rw [h1, show (0 : MMod F n) j = (0:ℚ) from rfl, mul_zero]
  | .inr t =>
    have h1 : (rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inr t0) : MMod F n) (Sum.inr t) = 0 := by
      rw [rhoBasis_Fof_inr]; simp [eNM_inl_inr_eq_zero]
    rw [h1]; ring

theorem rhoOp_Fof_Lof_inl_zero {F : FermionIndex} {n : ℕ} (w0 u v : I n) (j0 a : F.K) :
    rhoOp (Fof w0 j0 : OspBasis F n) (rhoBasis (Lof u v : OspBasis F n) (Sum.inl a)) = 0 := by
  have h0 : (rhoBasis (Lof u v : OspBasis F n) (Sum.inl a) : MMod F n) = 0 := by
    unfold Lof; split_ifs <;> unfold rhoBasis <;> rfl
  rw [h0]; unfold rhoOp; funext j; simp

theorem rhoOp_Fof_Lof_inr_inr_zero {F : FermionIndex} {n : ℕ} (w0 u v t0 : I n) (j0 : F.K)
    (s : I n) :
    rhoOp (Fof w0 j0 : OspBasis F n) (rhoBasis (Lof u v : OspBasis F n) (Sum.inr t0))
      (Sum.inr s) = 0 := by
  unfold rhoOp
  apply Finset.sum_eq_zero; intro l _
  match l with
  | .inl k =>
    have h1 : (rhoBasis (Lof u v : OspBasis F n) (Sum.inr t0) : MMod F n) (Sum.inl k) = 0 := by
      rw [rhoBasis_Lof]
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      rw [show (eNM (Sum.inr u) : MMod F n) (Sum.inl k) = 0 from by unfold eNM; simp,
          show (eNM (Sum.inr v) : MMod F n) (Sum.inl k) = 0 from by unfold eNM; simp]
      ring
    rw [h1]; ring
  | .inr t =>
    have h1 : (rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inr t) : MMod F n) (Sum.inr s) = 0 := by
      rw [rhoBasis_Fof_inr]; simp [eNM_inl_inr_eq_zero]
    rw [h1, mul_zero]

theorem rhoOp_Fof_Lof_inr_inl {F : FermionIndex} {n : ℕ} (w0 u v t0 : I n) (j0 a : F.K) :
    rhoOp (Fof w0 j0 : OspBasis F n) (rhoBasis (Lof u v : OspBasis F n) (Sum.inr t0)) (Sum.inl a)
      = (1/4 : ℚ) * (if a = j0 then (1:ℚ) else 0)
          * (J n v t0 * J n w0 u + J n u t0 * J n w0 v) := by
  unfold rhoOp
  have hsplit : (∑ l : Midx F n,
        (rhoBasis (Lof u v : OspBasis F n) (Sum.inr t0) : MMod F n) l
        * rhoBasis (Fof w0 j0 : OspBasis F n) l (Sum.inl a))
      = ∑ k : F.K, (rhoBasis (Lof u v : OspBasis F n) (Sum.inr t0) : MMod F n) (Sum.inl k)
          * rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inl k) (Sum.inl a)
        + ∑ l : I n, (rhoBasis (Lof u v : OspBasis F n) (Sum.inr t0) : MMod F n) (Sum.inr l)
          * rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inr l) (Sum.inl a) :=
    Fintype.sum_sum_type (fun l => (rhoBasis (Lof u v : OspBasis F n) (Sum.inr t0) : MMod F n) l
      * rhoBasis (Fof w0 j0 : OspBasis F n) l (Sum.inl a))
  rw [hsplit]
  have hz1 : (∑ k : F.K, (rhoBasis (Lof u v : OspBasis F n) (Sum.inr t0) : MMod F n) (Sum.inl k)
        * rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inl k) (Sum.inl a)) = 0 := by
    apply Finset.sum_eq_zero; intro k _
    rw [rhoBasis_Lof]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [show (eNM (Sum.inr u) : MMod F n) (Sum.inl k) = 0 from by unfold eNM; simp,
        show (eNM (Sum.inr v) : MMod F n) (Sum.inl k) = 0 from by unfold eNM; simp]
    ring
  rw [hz1, zero_add]
  have hexp : (∑ l : I n, (rhoBasis (Lof u v : OspBasis F n) (Sum.inr t0) : MMod F n) (Sum.inr l)
        * rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inr l) (Sum.inl a))
      = ∑ l : I n, ((1/2 : ℚ) * (J n v t0 * (if l = u then (1:ℚ) else 0)
          + J n u t0 * (if l = v then (1:ℚ) else 0)))
          * rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inr l) (Sum.inl a) := by
    apply Finset.sum_congr rfl; intro l _
    rw [rhoBasis_Lof]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, eNM_I_eq]
  rw [hexp]
  have hfac : (∑ l : I n, ((1/2 : ℚ) * (J n v t0 * (if l = u then (1:ℚ) else 0)
        + J n u t0 * (if l = v then (1:ℚ) else 0)))
        * rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inr l) (Sum.inl a))
      = (1/2 : ℚ) * J n v t0 * ∑ l : I n, (if l = u then (1:ℚ) else 0)
          * rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inr l) (Sum.inl a)
        + (1/2 : ℚ) * J n u t0 * ∑ l : I n, (if l = v then (1:ℚ) else 0)
          * rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inr l) (Sum.inl a) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro l _; split_ifs <;> ring
  rw [hfac]
  have hcu : (∑ l : I n, (if l = u then (1:ℚ) else 0)
        * rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inr l) (Sum.inl a))
      = rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inr u) (Sum.inl a) := by
    rw [Finset.sum_eq_single u]
    · simp
    · intro l _ hl; simp [hl]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hcv : (∑ l : I n, (if l = v then (1:ℚ) else 0)
        * rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inr l) (Sum.inl a))
      = rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inr v) (Sum.inl a) := by
    rw [Finset.sum_eq_single v]
    · simp
    · intro l _ hl; simp [hl]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hcu, hcv, rhoBasis_Fof_inr, rhoBasis_Fof_inr]
  simp only [Pi.smul_apply, smul_eq_mul, eNM_K_eq]
  ring

theorem rhoBasis_LF_rhs {F : FermionIndex} {n : ℕ} (u v w0 : I n) (j0 : F.K) (i : Midx F n) :
    (∑ k : OspBasis F n, (bracket0BasisQ (Lof u v : OspBasis F n) (Fof w0 j0 : OspBasis F n) k)
        • rhoBasis k i : MMod F n)
      = (1/2 * J n v w0) • rhoBasis (Fof u j0 : OspBasis F n) i
        + (1/2 * J n u w0) • rhoBasis (Fof v j0 : OspBasis F n) i := by
  have heq : (∑ k : OspBasis F n,
        bracket0BasisQ (Lof u v : OspBasis F n) (Fof w0 j0 : OspBasis F n) k • rhoBasis k i)
      = ∑ k : OspBasis F n, ((1/2 * J n v w0) * (if k = Fof u j0 then (1:ℚ) else 0)
          + (1/2 * J n u w0) * (if k = Fof v j0 then (1:ℚ) else 0)) • rhoBasis k i := by
    apply Finset.sum_congr rfl; intro k _
    rw [bracket0BasisQ_Lof_Fof]
  rw [heq]
  rw [show (∑ k : OspBasis F n, ((1/2 * J n v w0) * (if k = Fof u j0 then (1:ℚ) else 0)
          + (1/2 * J n u w0) * (if k = Fof v j0 then (1:ℚ) else 0)) • rhoBasis k i)
      = (∑ k : OspBasis F n, ((1/2 * J n v w0) * (if k = Fof u j0 then (1:ℚ) else 0))
        • rhoBasis k i)
        + (∑ k : OspBasis F n, ((1/2 * J n u w0) * (if k = Fof v j0 then (1:ℚ) else 0))
          • rhoBasis k i)
      from by rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _
              rw [← add_smul]]
  congr 1
  · rw [Finset.sum_eq_single (Fof u j0 : OspBasis F n)]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single (Fof v j0 : OspBasis F n)]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- The `L,F` sector at `i = inl a`: both `rhoOp` compositions collapse via
cross-block-vanishing arguments to a genuine (nonzero) computation only in the
`inr s` output component; `inl a'` output is `0` on both sides. -/
theorem rho_bracket_LF_inl {F : FermionIndex} {n : ℕ} (u v w0 : I n) (huv : IKey u ≤ IKey v)
    (j0 : F.K) (a : F.K) :
    (rhoOp (Lof u v : OspBasis F n) (rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inl a))
        - gsign (parity (Lof u v : OspBasis F n)) (parity (Fof w0 j0 : OspBasis F n))
          • rhoOp (Fof w0 j0 : OspBasis F n) (rhoBasis (Lof u v : OspBasis F n) (Sum.inl a)))
      = ∑ k : OspBasis F n, (bracket0BasisQ (Lof u v : OspBasis F n) (Fof w0 j0 : OspBasis F n) k)
          • rhoBasis k (Sum.inl a) := by
  have hpar1 : parity (Lof u v : OspBasis F n) = 0 := by unfold Lof; split_ifs; rfl
  have hpar2 : parity (Fof w0 j0 : OspBasis F n) = 1 := rfl
  rw [hpar1, hpar2, gsign_zero_left, one_smul,
    rhoOp_Fof_Lof_inl_zero w0 u v j0 a, sub_zero, rhoBasis_LF_rhs]
  funext j
  match j with
  | .inl a' =>
    rw [rhoOp_Lof_Fof_inl_inl]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [rhoBasis_Fof_inl, rhoBasis_Fof_inl]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (eNM (Sum.inr u) : MMod F n) (Sum.inl a') = 0 from by unfold eNM; simp,
        show (eNM (Sum.inr v) : MMod F n) (Sum.inl a') = 0 from by unfold eNM; simp]
    ring
  | .inr s =>
    rw [rhoOp_Lof_Fof_inl_inr]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [rhoBasis_Fof_inl, rhoBasis_Fof_inl]
    simp only [Pi.smul_apply, smul_eq_mul, eNM_I_eq]
    ring

/-- The `L,F` sector at `i = inr t0`: mirror of `rho_bracket_LF_inl`, with the
genuine computation now landing in the `inl a` output component. -/
theorem rho_bracket_LF_inr {F : FermionIndex} {n : ℕ} (u v w0 : I n) (huv : IKey u ≤ IKey v)
    (j0 : F.K) (t0 : I n) :
    (rhoOp (Lof u v : OspBasis F n) (rhoBasis (Fof w0 j0 : OspBasis F n) (Sum.inr t0))
        - gsign (parity (Lof u v : OspBasis F n)) (parity (Fof w0 j0 : OspBasis F n))
          • rhoOp (Fof w0 j0 : OspBasis F n) (rhoBasis (Lof u v : OspBasis F n) (Sum.inr t0)))
      = ∑ k : OspBasis F n, (bracket0BasisQ (Lof u v : OspBasis F n) (Fof w0 j0 : OspBasis F n) k)
          • rhoBasis k (Sum.inr t0) := by
  have hpar1 : parity (Lof u v : OspBasis F n) = 0 := by unfold Lof; split_ifs; rfl
  have hpar2 : parity (Fof w0 j0 : OspBasis F n) = 1 := rfl
  rw [hpar1, hpar2, gsign_zero_left, one_smul,
    rhoOp_Lof_Fof_inr_zero u v w0 j0 t0, zero_sub, rhoBasis_LF_rhs]
  funext j
  match j with
  | .inr s =>
    simp only [Pi.neg_apply]
    rw [rhoOp_Fof_Lof_inr_inr_zero]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [rhoBasis_Fof_inr, rhoBasis_Fof_inr]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (eNM (Sum.inl j0) : MMod F n) (Sum.inr s) = 0 from by unfold eNM; simp]
    ring
  | .inl a =>
    simp only [Pi.neg_apply]
    rw [rhoOp_Fof_Lof_inr_inl]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [rhoBasis_Fof_inr, rhoBasis_Fof_inr]
    simp only [Pi.smul_apply, smul_eq_mul, eNM_K_eq]
    rw [J_antisymm w0 u, J_antisymm w0 v]
    ring

/-- **The `L,F` sector of `rho_bracket`**, for arbitrary `i : Midx F n`. -/
theorem rho_bracket_LF {F : FermionIndex} {n : ℕ} (u v w0 : I n) (huv : IKey u ≤ IKey v)
    (j0 : F.K) (i : Midx F n) :
    (rhoOp (Lof u v : OspBasis F n) (rhoBasis (Fof w0 j0 : OspBasis F n) i)
        - gsign (parity (Lof u v : OspBasis F n)) (parity (Fof w0 j0 : OspBasis F n))
          • rhoOp (Fof w0 j0 : OspBasis F n) (rhoBasis (Lof u v : OspBasis F n) i))
      = ∑ k : OspBasis F n, (bracket0BasisQ (Lof u v : OspBasis F n) (Fof w0 j0 : OspBasis F n) k)
          • rhoBasis k i := by
  match i with
  | .inl a => exact rho_bracket_LF_inl u v w0 huv j0 a
  | .inr t0 => exact rho_bracket_LF_inr u v w0 huv j0 t0

theorem rhoBasis_S_inl {F : FermionIndex} {n : ℕ} (i j : F.K) (hij : F.key i < F.key j) (a : F.K) :
    (rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) (Sum.inl a) : MMod F n)
      = F.g j a • eNM (Sum.inl i) - F.g i a • eNM (Sum.inl j) := by
  unfold rhoBasis; rfl

theorem rhoBasis_S_inr_zero {F : FermionIndex} {n : ℕ} (i j : F.K) (hij : F.key i < F.key j)
    (t : I n) :
    (rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) (Sum.inr t) : MMod F n) = 0 := by
  unfold rhoBasis; rfl

theorem rhoOp_S_inr_zero {F : FermionIndex} {n : ℕ} (i j : F.K) (hij : F.key i < F.key j)
    (m : Midx F n → ℚ) (s : I n) :
    rhoOp (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) m (Sum.inr s) = 0 := by
  unfold rhoOp
  apply Finset.sum_eq_zero; intro l' _
  match l' with
  | .inl b =>
    rw [rhoBasis_S_inl]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (eNM (Sum.inl i) : MMod F n) (Sum.inr s) = 0 from by unfold eNM; simp,
        show (eNM (Sum.inl j) : MMod F n) (Sum.inr s) = 0 from by unfold eNM; simp]
    ring
  | .inr t =>
    rw [rhoBasis_S_inr_zero i j hij t, show (0 : MMod F n) (Sum.inr s) = (0:ℚ) from rfl, mul_zero]

theorem rhoOp_S_S_inl_inl {F : FermionIndex} {n : ℕ} (i j k l : F.K) (hij : F.key i < F.key j)
    (hkl : F.key k < F.key l) (a a' : F.K) :
    rhoOp (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n)
        (rhoBasis (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n) (Sum.inl a)) (Sum.inl a')
      = F.g l a * F.g j k * (if a' = i then (1:ℚ) else 0)
        - F.g l a * F.g i k * (if a' = j then (1:ℚ) else 0)
        - F.g k a * F.g j l * (if a' = i then (1:ℚ) else 0)
        + F.g k a * F.g i l * (if a' = j then (1:ℚ) else 0) := by
  unfold rhoOp
  have hsplit : (∑ l' : Midx F n,
        (rhoBasis (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n) (Sum.inl a) : MMod F n) l'
        * rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) l' (Sum.inl a'))
      = ∑ b : F.K,
        (rhoBasis (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n) (Sum.inl a) : MMod F n)
          (Sum.inl b)
          * rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) (Sum.inl b) (Sum.inl a')
        + ∑ t : I n, (rhoBasis (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n) (Sum.inl a)
              : MMod F n) (Sum.inr t)
          * rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) (Sum.inr t) (Sum.inl a') :=
    Fintype.sum_sum_type
      (fun l' => (rhoBasis (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n) (Sum.inl a)
            : MMod F n) l'
        * rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) l' (Sum.inl a'))
  rw [hsplit]
  have hz : (∑ t : I n, (rhoBasis (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n) (Sum.inl a)
        : MMod F n) (Sum.inr t)
        * rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) (Sum.inr t) (Sum.inl a')) = 0 :=
          by
    apply Finset.sum_eq_zero; intro t _
    rw [rhoBasis_S_inr_zero i j hij t, show (0 : MMod F n) (Sum.inl a') = (0:ℚ) from rfl, mul_zero]
  rw [hz, add_zero]
  have hexp : (∑ b : F.K,
        (rhoBasis (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n) (Sum.inl a) : MMod F n)
          (Sum.inl b)
          * rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) (Sum.inl b) (Sum.inl a'))
      = ∑ b : F.K, (F.g l a * (if b = k then (1:ℚ) else 0) - F.g k a * (if b = l then (1:ℚ) else 0))
          * rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) (Sum.inl b) (Sum.inl a') := by
    apply Finset.sum_congr rfl; intro b _
    rw [rhoBasis_S_inl]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eNM_K_eq]
  rw [hexp]
  have hfac : (∑ b : F.K,
        (F.g l a * (if b = k then (1:ℚ) else 0) - F.g k a * (if b = l then (1:ℚ) else 0))
          * rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) (Sum.inl b) (Sum.inl a'))
      = F.g l a * ∑ b : F.K, (if b = k then (1:ℚ) else 0)
          * rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) (Sum.inl b) (Sum.inl a')
        - F.g k a * ∑ b : F.K, (if b = l then (1:ℚ) else 0)
          * rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) (Sum.inl b) (Sum.inl a') := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro b _; split_ifs <;> ring
  rw [hfac]
  have hck : (∑ b : F.K, (if b = k then (1:ℚ) else 0)
        * rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) (Sum.inl b) (Sum.inl a'))
      = rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) (Sum.inl k) (Sum.inl a') := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hcl : (∑ b : F.K, (if b = l then (1:ℚ) else 0)
        * rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) (Sum.inl b) (Sum.inl a'))
      = rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) (Sum.inl l) (Sum.inl a') := by
    rw [Finset.sum_eq_single l]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hck, hcl, rhoBasis_S_inl, rhoBasis_S_inl]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eNM_K_eq]
  ring

noncomputable def SofRho {F : FermionIndex} {n : ℕ} (p q : F.K) (m : Midx F n) : MMod F n :=
  if h : F.key p < F.key q then rhoBasis (Sum.inr (Sum.inl ⟨(p, q), h⟩) : OspBasis F n) m
  else if h2 : F.key q < F.key p then
    -rhoBasis (Sum.inr (Sum.inl ⟨(q, p), h2⟩) : OspBasis F n) m
  else 0

theorem SofRho_inr_zero {F : FermionIndex} {n : ℕ} (p q : F.K) (t : I n) :
    SofRho p q (Sum.inr t : Midx F n) = 0 := by
  unfold SofRho
  split_ifs with h h2
  · exact rhoBasis_S_inr_zero p q h t
  · rw [rhoBasis_S_inr_zero q p h2]; simp
  · rfl

theorem SofRho_inl_inl {F : FermionIndex} {n : ℕ} (p q a a' : F.K) :
    (SofRho p q (Sum.inl a : Midx F n) : MMod F n) (Sum.inl a')
      = F.g q a * (if a' = p then (1:ℚ) else 0) - F.g p a * (if a' = q then (1:ℚ) else 0) := by
  rcases lt_trichotomy (F.key p) (F.key q) with h | h | h
  · unfold SofRho
    rw [dite_eq_left h, rhoBasis_S_inl]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eNM_K_eq]
  · have hpq : p = q := F.key_injective h
    subst hpq
    unfold SofRho
    rw [dite_eq_right (lt_irrefl _), dite_eq_right (lt_irrefl _),
      show (0 : MMod F n) (Sum.inl a') = (0:ℚ) from rfl]
    ring
  · unfold SofRho
    rw [dite_eq_right (not_lt.mpr h.le), dite_eq_left h,
      show (-rhoBasis (Sum.inr (Sum.inl ⟨(q, p), h⟩) : OspBasis F n) (Sum.inl a) : MMod F n)
          (Sum.inl a')
        = -(rhoBasis (Sum.inr (Sum.inl ⟨(q, p), h⟩) : OspBasis F n) (Sum.inl a) : MMod F n)
            (Sum.inl a') from rfl,
      rhoBasis_S_inl]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eNM_K_eq]
    ring

theorem SofRho_inl_inr_zero {F : FermionIndex} {n : ℕ} (p q a : F.K) (s : I n) :
    (SofRho p q (Sum.inl a : Midx F n) : MMod F n) (Sum.inr s) = 0 := by
  unfold SofRho
  split_ifs with h h2
  · rw [rhoBasis_S_inl]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (eNM (Sum.inl p) : MMod F n) (Sum.inr s) = 0 from by unfold eNM; simp,
        show (eNM (Sum.inl q) : MMod F n) (Sum.inr s) = 0 from by unfold eNM; simp]
    ring
  · rw [show (-rhoBasis (Sum.inr (Sum.inl ⟨(q, p), h2⟩) : OspBasis F n) (Sum.inl a) : MMod F n)
        (Sum.inr s)
        = -(rhoBasis (Sum.inr (Sum.inl ⟨(q, p), h2⟩) : OspBasis F n) (Sum.inl a) : MMod F n)
            (Sum.inr s) from rfl,
      rhoBasis_S_inl]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (eNM (Sum.inl q) : MMod F n) (Sum.inr s) = 0 from by unfold eNM; simp,
        show (eNM (Sum.inl p) : MMod F n) (Sum.inr s) = 0 from by unfold eNM; simp]
    ring
  · rfl

theorem bracket0BasisQ_S_S {F : FermionIndex} {n : ℕ} (i j k l : F.K) (hij : F.key i < F.key j)
    (hkl : F.key k < F.key l) (k' : OspBasis F n) :
    bracket0BasisQ (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n)
        (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n) k'
      = F.g j k * (MvPolynomial.constantCoeff (Sof i l k' : Pmn F n) : ℚ)
        - F.g i k * (MvPolynomial.constantCoeff (Sof j l k' : Pmn F n) : ℚ)
        - F.g j l * (MvPolynomial.constantCoeff (Sof i k k' : Pmn F n) : ℚ)
        + F.g i l * (MvPolynomial.constantCoeff (Sof j k k' : Pmn F n) : ℚ) := by
  unfold bracket0BasisQ bracket0Basis bracketSS
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  rw [map_add, map_sub, map_sub, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def,
    Algebra.smul_def, map_mul, map_mul, map_mul, map_mul]
  simp

theorem rho_sum_eN {F : FermionIndex} {n : ℕ} (b : OspBasis F n) (m : Midx F n) :
    (∑ k' : OspBasis F n, (if k' = b then (1:ℚ) else 0) • rhoBasis k' m : MMod F n)
      = rhoBasis b m := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro k' _ hk'; simp [hk']
  · intro h; exact absurd (Finset.mem_univ _) h

theorem rho_sum_neg_eN {F : FermionIndex} {n : ℕ} (b : OspBasis F n) (m : Midx F n) :
    (∑ k' : OspBasis F n, (if k' = b then (-1:ℚ) else 0) • rhoBasis k' m : MMod F n)
      = -rhoBasis b m := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro k' _ hk'; simp [hk']
  · intro h; exact absurd (Finset.mem_univ _) h

theorem bracket0BasisQ_Sof_apply {F : FermionIndex} {n : ℕ} (p q : F.K) (k' : OspBasis F n) :
    (MvPolynomial.constantCoeff (Sof p q k' : Pmn F n) : ℚ)
      = if h : F.key p < F.key q then (if k' = Sum.inr (Sum.inl ⟨(p, q), h⟩) then (1:ℚ) else 0)
        else if h2 : F.key q < F.key p then
          (if k' = Sum.inr (Sum.inl ⟨(q, p), h2⟩) then (-1:ℚ) else 0)
        else 0 := by
  unfold Sof eN
  split_ifs with h h2 h3 h4 <;>
    simp_all

theorem rho_sum_Sof {F : FermionIndex} {n : ℕ} (p q : F.K) (m : Midx F n) :
    (∑ k' : OspBasis F n, (MvPolynomial.constantCoeff (Sof p q k' : Pmn F n) : ℚ) • rhoBasis k' m
        : MMod F n)
      = SofRho p q m := by
  unfold SofRho
  split_ifs with h h2
  · rw [show (∑ k' : OspBasis F n,
          (MvPolynomial.constantCoeff (Sof p q k' : Pmn F n) : ℚ) • rhoBasis k' m)
        = ∑ k' : OspBasis F n,
          (if k' = (Sum.inr (Sum.inl ⟨(p, q), h⟩) : OspBasis F n) then (1:ℚ) else 0)
            • rhoBasis k' m
      from by apply Finset.sum_congr rfl; intro k' _
              rw [bracket0BasisQ_Sof_apply]; simp [h]]
    exact rho_sum_eN _ m
  · rw [show (∑ k' : OspBasis F n,
          (MvPolynomial.constantCoeff (Sof p q k' : Pmn F n) : ℚ) • rhoBasis k' m)
        = ∑ k' : OspBasis F n,
          (if k' = (Sum.inr (Sum.inl ⟨(q, p), h2⟩) : OspBasis F n) then (-1:ℚ) else 0)
            • rhoBasis k' m
      from by apply Finset.sum_congr rfl; intro k' _
              rw [bracket0BasisQ_Sof_apply]; simp [h, h2]]
    exact rho_sum_neg_eN _ m
  · apply Finset.sum_eq_zero; intro k' _
    rw [bracket0BasisQ_Sof_apply]; simp [h, h2]

theorem rhoBasis_SS_rhs {F : FermionIndex} {n : ℕ} (i j k l : F.K) (hij : F.key i < F.key j)
    (hkl : F.key k < F.key l) (m : Midx F n) :
    (∑ k' : OspBasis F n,
        (bracket0BasisQ (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n)
            (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n) k') • rhoBasis k' m : MMod F n)
      = F.g j k • SofRho i l m - F.g i k • SofRho j l m - F.g j l • SofRho i k m
        + F.g i l • SofRho j k m := by
  have heq : (∑ k' : OspBasis F n,
        bracket0BasisQ (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n)
            (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n) k' • rhoBasis k' m)
      = ∑ k' : OspBasis F n,
        ((F.g j k * (MvPolynomial.constantCoeff (Sof i l k' : Pmn F n) : ℚ)) • rhoBasis k' m
          - (F.g i k * (MvPolynomial.constantCoeff (Sof j l k' : Pmn F n) : ℚ)) • rhoBasis k' m
          - (F.g j l * (MvPolynomial.constantCoeff (Sof i k k' : Pmn F n) : ℚ)) • rhoBasis k' m
          + (F.g i l * (MvPolynomial.constantCoeff (Sof j k k' : Pmn F n) : ℚ)) • rhoBasis k' m) :=
            by
    apply Finset.sum_congr rfl; intro k' _
    rw [bracket0BasisQ_S_S]
    simp [sub_smul, add_smul]
  rw [heq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [show (∑ k' : OspBasis F n,
        (F.g j k * (MvPolynomial.constantCoeff (Sof i l k' : Pmn F n) : ℚ)) • rhoBasis k' m)
      = F.g j k • (∑ k' : OspBasis F n,
          (MvPolynomial.constantCoeff (Sof i l k' : Pmn F n) : ℚ) • rhoBasis k' m)
      from by rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro k' _; rw [smul_smul]]
  rw [show (∑ k' : OspBasis F n,
        (F.g i k * (MvPolynomial.constantCoeff (Sof j l k' : Pmn F n) : ℚ)) • rhoBasis k' m)
      = F.g i k • (∑ k' : OspBasis F n,
          (MvPolynomial.constantCoeff (Sof j l k' : Pmn F n) : ℚ) • rhoBasis k' m)
      from by rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro k' _; rw [smul_smul]]
  rw [show (∑ k' : OspBasis F n,
        (F.g j l * (MvPolynomial.constantCoeff (Sof i k k' : Pmn F n) : ℚ)) • rhoBasis k' m)
      = F.g j l • (∑ k' : OspBasis F n,
          (MvPolynomial.constantCoeff (Sof i k k' : Pmn F n) : ℚ) • rhoBasis k' m)
      from by rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro k' _; rw [smul_smul]]
  rw [show (∑ k' : OspBasis F n,
        (F.g i l * (MvPolynomial.constantCoeff (Sof j k k' : Pmn F n) : ℚ)) • rhoBasis k' m)
      = F.g i l • (∑ k' : OspBasis F n,
          (MvPolynomial.constantCoeff (Sof j k k' : Pmn F n) : ℚ) • rhoBasis k' m)
      from by rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro k' _; rw [smul_smul]]
  rw [rho_sum_Sof, rho_sum_Sof, rho_sum_Sof, rho_sum_Sof]

/-- The `S,S` sector at `m = inr t`: both sides `0` outright, since `S`-kind's own
`rhoBasis` is zero at any `inr` selector, and `SofRho` is likewise zero at any `inr`
selector. -/
theorem rho_bracket_SS_inr {F : FermionIndex} {n : ℕ} (i j k l : F.K) (hij : F.key i < F.key j)
    (hkl : F.key k < F.key l) (t : I n) :
    (rhoOp (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n)
        (rhoBasis (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n) (Sum.inr t))
        - gsign (parity (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n))
            (parity (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n))
          • rhoOp (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n)
              (rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) (Sum.inr t)))
      = ∑ k' : OspBasis F n, (bracket0BasisQ (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n)
            (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n) k')
          • rhoBasis k' (Sum.inr t) := by
  rw [rhoBasis_S_inr_zero k l hkl t, rhoBasis_S_inr_zero i j hij t]
  have hop1 : rhoOp (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) (0 : MMod F n) = 0 := by
    unfold rhoOp; funext j'; simp
  have hop2 : rhoOp (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n) (0 : MMod F n) = 0 := by
    unfold rhoOp; funext j'; simp
  rw [hop1, hop2, smul_zero, sub_zero, rhoBasis_SS_rhs]
  rw [SofRho_inr_zero, SofRho_inr_zero, SofRho_inr_zero, SofRho_inr_zero]
  simp

/-- The `S,S` sector at `m = inl a`: the genuine computation, at output `inl a'`
(output `inr s` vanishes on both sides trivially). `F.g_symm` normalizes the
reversed-order `F.g` terms that appear from swapping `(i,j) ↔ (k,l)` before `ring`
closes the resulting identity. -/
theorem rho_bracket_SS_inl {F : FermionIndex} {n : ℕ} (i j k l : F.K) (hij : F.key i < F.key j)
    (hkl : F.key k < F.key l) (a : F.K) :
    (rhoOp (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n)
        (rhoBasis (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n) (Sum.inl a))
        - gsign (parity (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n))
            (parity (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n))
          • rhoOp (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n)
              (rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) (Sum.inl a)))
      = ∑ k' : OspBasis F n, (bracket0BasisQ (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n)
            (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n) k')
          • rhoBasis k' (Sum.inl a) := by
  rw [show parity (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) = 0 from rfl,
    show parity (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n) = 0 from rfl,
    gsign_zero_left, one_smul, rhoBasis_SS_rhs]
  funext j'
  match j' with
  | .inr s =>
    simp only [Pi.sub_apply]
    rw [rhoOp_S_inr_zero i j hij, rhoOp_S_inr_zero k l hkl]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      SofRho_inl_inr_zero]
    ring
  | .inl a' =>
    simp only [Pi.sub_apply]
    rw [rhoOp_S_S_inl_inl, rhoOp_S_S_inl_inl]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, SofRho_inl_inl]
    rw [F.g_symm l i, F.g_symm k i, F.g_symm k j, F.g_symm l j]
    split_ifs <;> ring

/-- **The `S,S` sector of `rho_bracket`**, for arbitrary `m : Midx F n`. -/
theorem rho_bracket_SS {F : FermionIndex} {n : ℕ} (i j k l : F.K) (hij : F.key i < F.key j)
    (hkl : F.key k < F.key l) (m : Midx F n) :
    (rhoOp (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n)
        (rhoBasis (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n) m)
        - gsign (parity (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n))
            (parity (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n))
          • rhoOp (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n)
              (rhoBasis (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) m))
      = ∑ k' : OspBasis F n, (bracket0BasisQ (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n)
            (Sum.inr (Sum.inl ⟨(k, l), hkl⟩) : OspBasis F n) k')
          • rhoBasis k' m := by
  match m with
  | .inl a => exact rho_bracket_SS_inl i j k l hij hkl a
  | .inr t => exact rho_bracket_SS_inr i j k l hij hkl t

theorem rhoOp_S_Fof_inl_zero {F : FermionIndex} {n : ℕ} (j k : F.K) (hjk : F.key j < F.key k)
    (w : I n) (i a : F.K) :
    rhoOp (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n)
      (rhoBasis (Fof w i : OspBasis F n) (Sum.inl a)) = 0 := by
  unfold rhoOp; funext j'
  apply Finset.sum_eq_zero; intro l' _
  match l' with
  | .inl b =>
    have h1 : (rhoBasis (Fof w i : OspBasis F n) (Sum.inl a) : MMod F n) (Sum.inl b) = 0 := by
      rw [rhoBasis_Fof_inl]; simp [eNM_inr_inl_eq_zero]
    rw [h1, zero_mul]
  | .inr t =>
    rw [rhoBasis_S_inr_zero j k hjk t, show (0 : MMod F n) j' = (0:ℚ) from rfl, mul_zero]

theorem rhoOp_Fof_S_inr_zero {F : FermionIndex} {n : ℕ} (w : I n) (i : F.K) (j k : F.K)
    (hjk : F.key j < F.key k) (t0 : I n) :
    rhoOp (Fof w i : OspBasis F n)
      (rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Sum.inr t0)) = 0 := by
  rw [rhoBasis_S_inr_zero j k hjk t0]
  unfold rhoOp; funext j'; simp

theorem rhoOp_S_Fof_inr {F : FermionIndex} {n : ℕ} (j k : F.K) (hjk : F.key j < F.key k)
    (w : I n) (i : F.K) (t0 : I n) (jout : Midx F n) :
    rhoOp (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n)
        (rhoBasis (Fof w i : OspBasis F n) (Sum.inr t0)) jout
      = (1/2:ℚ) * J n w t0
          * (F.g k i * (eNM (Sum.inl j) : MMod F n) jout
             - F.g j i * (eNM (Sum.inl k) : MMod F n) jout) := by
  unfold rhoOp
  have hsplit : (∑ l' : Midx F n,
        (rhoBasis (Fof w i : OspBasis F n) (Sum.inr t0) : MMod F n) l'
        * rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) l' jout)
      = ∑ b : F.K, (rhoBasis (Fof w i : OspBasis F n) (Sum.inr t0) : MMod F n) (Sum.inl b)
          * rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Sum.inl b) jout
        + ∑ t : I n, (rhoBasis (Fof w i : OspBasis F n) (Sum.inr t0) : MMod F n) (Sum.inr t)
          * rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Sum.inr t) jout :=
    Fintype.sum_sum_type (fun l' => (rhoBasis (Fof w i : OspBasis F n) (Sum.inr t0) : MMod F n) l'
      * rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) l' jout)
  rw [hsplit]
  have hz : (∑ t : I n, (rhoBasis (Fof w i : OspBasis F n) (Sum.inr t0) : MMod F n) (Sum.inr t)
        * rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Sum.inr t) jout) = 0 := by
    apply Finset.sum_eq_zero; intro t _
    rw [rhoBasis_S_inr_zero j k hjk t, show (0 : MMod F n) jout = (0:ℚ) from rfl, mul_zero]
  rw [hz, add_zero]
  have hexp : (∑ b : F.K, (rhoBasis (Fof w i : OspBasis F n) (Sum.inr t0) : MMod F n) (Sum.inl b)
        * rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Sum.inl b) jout)
      = ∑ b : F.K, ((1/2:ℚ) * J n w t0 * (if b = i then (1:ℚ) else 0))
          * rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Sum.inl b) jout := by
    apply Finset.sum_congr rfl; intro b _
    rw [rhoBasis_Fof_inr]
    simp only [Pi.smul_apply, smul_eq_mul, eNM_K_eq]
    split_ifs <;> ring
  rw [hexp]
  have hfac : (∑ b : F.K, ((1/2:ℚ) * J n w t0 * (if b = i then (1:ℚ) else 0))
        * rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Sum.inl b) jout)
      = (1/2:ℚ) * J n w t0 * ∑ b : F.K, (if b = i then (1:ℚ) else 0)
          * rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Sum.inl b) jout := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; split_ifs <;> ring
  rw [hfac]
  have hc : (∑ b : F.K, (if b = i then (1:ℚ) else 0)
        * rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Sum.inl b) jout)
      = rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Sum.inl i) jout := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hc, rhoBasis_S_inl]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

theorem rhoOp_Fof_S_inl {F : FermionIndex} {n : ℕ} (w : I n) (i j k : F.K)
    (hjk : F.key j < F.key k) (a : F.K) (jout : Midx F n) :
    rhoOp (Fof w i : OspBasis F n)
        (rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Sum.inl a)) jout
      = (1/2:ℚ) * (F.g k a * F.g i j - F.g j a * F.g i k)
          * (eNM (Sum.inr w) : MMod F n) jout := by
  unfold rhoOp
  have hsplit : (∑ l' : Midx F n,
        (rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Sum.inl a) : MMod F n) l'
        * rhoBasis (Fof w i : OspBasis F n) l' jout)
      = ∑ b : F.K, (rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Sum.inl a)
            : MMod F n) (Sum.inl b) * rhoBasis (Fof w i : OspBasis F n) (Sum.inl b) jout
        + ∑ t : I n, (rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Sum.inl a)
              : MMod F n) (Sum.inr t) * rhoBasis (Fof w i : OspBasis F n) (Sum.inr t) jout :=
    Fintype.sum_sum_type (fun l' =>
      (rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Sum.inl a) : MMod F n) l'
        * rhoBasis (Fof w i : OspBasis F n) l' jout)
  rw [hsplit]
  have hz : (∑ t : I n, (rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Sum.inl a)
        : MMod F n) (Sum.inr t) * rhoBasis (Fof w i : OspBasis F n) (Sum.inr t) jout) = 0 := by
    apply Finset.sum_eq_zero; intro t _
    have h1 : (rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Sum.inl a)
        : MMod F n) (Sum.inr t) = 0 := by
      rw [rhoBasis_S_inl]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [show (eNM (Sum.inl j) : MMod F n) (Sum.inr t) = 0 from by unfold eNM; simp,
          show (eNM (Sum.inl k) : MMod F n) (Sum.inr t) = 0 from by unfold eNM; simp]
      ring
    rw [h1, zero_mul]
  rw [hz, add_zero]
  have hexp : (∑ b : F.K, (rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Sum.inl a)
        : MMod F n) (Sum.inl b) * rhoBasis (Fof w i : OspBasis F n) (Sum.inl b) jout)
      = ∑ b : F.K, ((F.g k a) * (if b = j then (1:ℚ) else 0)
          - (F.g j a) * (if b = k then (1:ℚ) else 0))
          * rhoBasis (Fof w i : OspBasis F n) (Sum.inl b) jout := by
    apply Finset.sum_congr rfl; intro b _
    rw [rhoBasis_S_inl]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eNM_K_eq]
  rw [hexp]
  have hfac : (∑ b : F.K, ((F.g k a) * (if b = j then (1:ℚ) else 0)
        - (F.g j a) * (if b = k then (1:ℚ) else 0))
        * rhoBasis (Fof w i : OspBasis F n) (Sum.inl b) jout)
      = F.g k a * ∑ b : F.K, (if b = j then (1:ℚ) else 0)
          * rhoBasis (Fof w i : OspBasis F n) (Sum.inl b) jout
        - F.g j a * ∑ b : F.K, (if b = k then (1:ℚ) else 0)
          * rhoBasis (Fof w i : OspBasis F n) (Sum.inl b) jout := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro b _; split_ifs <;> ring
  rw [hfac]
  have hcj : (∑ b : F.K, (if b = j then (1:ℚ) else 0)
        * rhoBasis (Fof w i : OspBasis F n) (Sum.inl b) jout)
      = rhoBasis (Fof w i : OspBasis F n) (Sum.inl j) jout := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hck : (∑ b : F.K, (if b = k then (1:ℚ) else 0)
        * rhoBasis (Fof w i : OspBasis F n) (Sum.inl b) jout)
      = rhoBasis (Fof w i : OspBasis F n) (Sum.inl k) jout := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hcj, hck, rhoBasis_Fof_inl, rhoBasis_Fof_inl]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem bracket0BasisQ_S_F {F : FermionIndex} {n : ℕ} (j k : F.K) (hjk : F.key j < F.key k)
    (w : I n) (i : F.K) (k' : OspBasis F n) :
    bracket0BasisQ (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Fof w i : OspBasis F n) k'
      = F.g k i * (if k' = Fof w j then (1:ℚ) else 0)
        - F.g j i * (if k' = Fof w k then (1:ℚ) else 0) := by
  unfold bracket0BasisQ bracket0Basis bracketSF Fof
  simp only [Pi.sub_apply, Pi.smul_apply]
  rw [eN_eq_algebraMap, eN_eq_algebraMap]
  simp only [Algebra.algebraMap_eq_smul_one, smul_smul]
  split_ifs <;> simp

theorem rhoBasis_SF_rhs {F : FermionIndex} {n : ℕ} (j k : F.K) (hjk : F.key j < F.key k)
    (w : I n) (i : F.K) (m : Midx F n) :
    (∑ k' : OspBasis F n,
        (bracket0BasisQ (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n)
            (Fof w i : OspBasis F n) k') • rhoBasis k' m : MMod F n)
      = F.g k i • rhoBasis (Fof w j : OspBasis F n) m
        - F.g j i • rhoBasis (Fof w k : OspBasis F n) m := by
  have heq : (∑ k' : OspBasis F n,
        bracket0BasisQ (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n)
            (Fof w i : OspBasis F n) k' • rhoBasis k' m)
      = ∑ k' : OspBasis F n, (F.g k i * (if k' = Fof w j then (1:ℚ) else 0)
          - F.g j i * (if k' = Fof w k then (1:ℚ) else 0)) • rhoBasis k' m := by
    apply Finset.sum_congr rfl; intro k' _
    rw [bracket0BasisQ_S_F]
  rw [heq]
  rw [show (∑ k' : OspBasis F n, (F.g k i * (if k' = Fof w j then (1:ℚ) else 0)
          - F.g j i * (if k' = Fof w k then (1:ℚ) else 0)) • rhoBasis k' m)
      = (∑ k' : OspBasis F n, (F.g k i * (if k' = Fof w j then (1:ℚ) else 0)) • rhoBasis k' m)
        - (∑ k' : OspBasis F n, (F.g j i * (if k' = Fof w k then (1:ℚ) else 0)) • rhoBasis k' m)
      from by rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro k' _
              rw [sub_smul]]
  congr 1
  · rw [Finset.sum_eq_single (Fof w j : OspBasis F n)]
    · simp
    · intro k' _ hk'; simp [hk']
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single (Fof w k : OspBasis F n)]
    · simp
    · intro k' _ hk'; simp [hk']
    · intro h; exact absurd (Finset.mem_univ _) h

/-- The `S,F` sector at `m = inl a`: the genuine computation lands in the `inr w`
output component of the cross term; the `F.g_symm` normalization is needed to match
the reversed-argument `F.g` terms produced by the two directions of the cross
term. -/
theorem rho_bracket_SF_inl {F : FermionIndex} {n : ℕ} (j k : F.K) (hjk : F.key j < F.key k)
    (w : I n) (i a : F.K) :
    (rhoOp (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (rhoBasis (Fof w i : OspBasis F n)
          (Sum.inl a))
        - gsign (parity (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n)) (parity (Fof w i))
          • rhoOp (Fof w i : OspBasis F n)
              (rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Sum.inl a)))
      = ∑ k' : OspBasis F n,
          (bracket0BasisQ (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Fof w i : OspBasis F n)
              k') • rhoBasis k' (Sum.inl a) := by
  rw [show parity (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) = 0 from rfl,
    show parity (Fof w i : OspBasis F n) = 1 from rfl, gsign_zero_left, one_smul,
    rhoOp_S_Fof_inl_zero, zero_sub, rhoBasis_SF_rhs]
  funext jout
  simp only [Pi.neg_apply]
  rw [rhoOp_Fof_S_inl]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [rhoBasis_Fof_inl, rhoBasis_Fof_inl]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [F.g_symm k i, F.g_symm j i]
  ring

/-- The `S,F` sector at `m = inr t0`: the genuine computation lands in the `inl`
components; no `F.g_symm` normalization needed here, unlike the `inl a` case. -/
theorem rho_bracket_SF_inr {F : FermionIndex} {n : ℕ} (j k : F.K) (hjk : F.key j < F.key k)
    (w : I n) (i : F.K) (t0 : I n) :
    (rhoOp (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (rhoBasis (Fof w i : OspBasis F n)
          (Sum.inr t0))
        - gsign (parity (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n)) (parity (Fof w i))
          • rhoOp (Fof w i : OspBasis F n)
              (rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Sum.inr t0)))
      = ∑ k' : OspBasis F n,
          (bracket0BasisQ (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Fof w i : OspBasis F n)
              k') • rhoBasis k' (Sum.inr t0) := by
  rw [show parity (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) = 0 from rfl,
    show parity (Fof w i : OspBasis F n) = 1 from rfl, gsign_zero_left, one_smul,
    rhoOp_Fof_S_inr_zero, sub_zero, rhoBasis_SF_rhs]
  funext jout
  rw [rhoOp_S_Fof_inr]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [rhoBasis_Fof_inr, rhoBasis_Fof_inr]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **The `S,F` sector of `rho_bracket`**, for arbitrary `m : Midx F n`. -/
theorem rho_bracket_SF {F : FermionIndex} {n : ℕ} (j k : F.K) (hjk : F.key j < F.key k)
    (w : I n) (i : F.K) (m : Midx F n) :
    (rhoOp (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (rhoBasis (Fof w i : OspBasis F n) m)
        - gsign (parity (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n)) (parity (Fof w i))
          • rhoOp (Fof w i : OspBasis F n)
              (rhoBasis (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) m))
      = ∑ k' : OspBasis F n,
          (bracket0BasisQ (Sum.inr (Sum.inl ⟨(j, k), hjk⟩) : OspBasis F n) (Fof w i : OspBasis F n)
              k') • rhoBasis k' m := by
  match m with
  | .inl a => exact rho_bracket_SF_inl j k hjk w i a
  | .inr t0 => exact rho_bracket_SF_inr j k hjk w i t0

theorem rhoOp_Fof_Fof_inl {F : FermionIndex} {n : ℕ} (u v : I n) (i j a : F.K) (jout : Midx F n) :
    rhoOp (Fof u i : OspBasis F n) (rhoBasis (Fof v j : OspBasis F n) (Sum.inl a)) jout
      = (1/4:ℚ) * F.g j a * J n u v * (eNM (Sum.inl i) : MMod F n) jout := by
  unfold rhoOp
  have hsplit : (∑ l' : Midx F n,
        (rhoBasis (Fof v j : OspBasis F n) (Sum.inl a) : MMod F n) l'
        * rhoBasis (Fof u i : OspBasis F n) l' jout)
      = ∑ b : F.K, (rhoBasis (Fof v j : OspBasis F n) (Sum.inl a) : MMod F n) (Sum.inl b)
          * rhoBasis (Fof u i : OspBasis F n) (Sum.inl b) jout
        + ∑ t : I n, (rhoBasis (Fof v j : OspBasis F n) (Sum.inl a) : MMod F n) (Sum.inr t)
          * rhoBasis (Fof u i : OspBasis F n) (Sum.inr t) jout :=
    Fintype.sum_sum_type (fun l' => (rhoBasis (Fof v j : OspBasis F n) (Sum.inl a) : MMod F n) l'
      * rhoBasis (Fof u i : OspBasis F n) l' jout)
  rw [hsplit]
  have hz : (∑ b : F.K, (rhoBasis (Fof v j : OspBasis F n) (Sum.inl a) : MMod F n) (Sum.inl b)
        * rhoBasis (Fof u i : OspBasis F n) (Sum.inl b) jout) = 0 := by
    apply Finset.sum_eq_zero; intro b _
    have h1 : (rhoBasis (Fof v j : OspBasis F n) (Sum.inl a) : MMod F n) (Sum.inl b) = 0 := by
      rw [rhoBasis_Fof_inl]; simp [eNM_inr_inl_eq_zero]
    rw [h1, zero_mul]
  rw [hz, zero_add]
  have hexp : (∑ t : I n, (rhoBasis (Fof v j : OspBasis F n) (Sum.inl a) : MMod F n) (Sum.inr t)
        * rhoBasis (Fof u i : OspBasis F n) (Sum.inr t) jout)
      = ∑ t : I n, ((1/2:ℚ) * F.g j a * (if t = v then (1:ℚ) else 0))
          * rhoBasis (Fof u i : OspBasis F n) (Sum.inr t) jout := by
    apply Finset.sum_congr rfl; intro t _
    rw [rhoBasis_Fof_inl]
    simp only [Pi.smul_apply, smul_eq_mul, eNM_I_eq]
    split_ifs <;> ring
  rw [hexp]
  have hfac : (∑ t : I n, ((1/2:ℚ) * F.g j a * (if t = v then (1:ℚ) else 0))
        * rhoBasis (Fof u i : OspBasis F n) (Sum.inr t) jout)
      = (1/2:ℚ) * F.g j a * ∑ t : I n, (if t = v then (1:ℚ) else 0)
          * rhoBasis (Fof u i : OspBasis F n) (Sum.inr t) jout := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t _; split_ifs <;> ring
  rw [hfac]
  have hc : (∑ t : I n, (if t = v then (1:ℚ) else 0)
        * rhoBasis (Fof u i : OspBasis F n) (Sum.inr t) jout)
      = rhoBasis (Fof u i : OspBasis F n) (Sum.inr v) jout := by
    rw [Finset.sum_eq_single v]
    · simp
    · intro t _ ht; simp [ht]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hc, rhoBasis_Fof_inr]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem rhoOp_Fof_Fof_inr {F : FermionIndex} {n : ℕ} (u v : I n) (i j : F.K) (t0 : I n)
    (jout : Midx F n) :
    rhoOp (Fof u i : OspBasis F n) (rhoBasis (Fof v j : OspBasis F n) (Sum.inr t0)) jout
      = (1/4:ℚ) * J n v t0 * F.g i j * (eNM (Sum.inr u) : MMod F n) jout := by
  unfold rhoOp
  have hsplit : (∑ l' : Midx F n,
        (rhoBasis (Fof v j : OspBasis F n) (Sum.inr t0) : MMod F n) l'
        * rhoBasis (Fof u i : OspBasis F n) l' jout)
      = ∑ b : F.K, (rhoBasis (Fof v j : OspBasis F n) (Sum.inr t0) : MMod F n) (Sum.inl b)
          * rhoBasis (Fof u i : OspBasis F n) (Sum.inl b) jout
        + ∑ t : I n, (rhoBasis (Fof v j : OspBasis F n) (Sum.inr t0) : MMod F n) (Sum.inr t)
          * rhoBasis (Fof u i : OspBasis F n) (Sum.inr t) jout :=
    Fintype.sum_sum_type (fun l' => (rhoBasis (Fof v j : OspBasis F n) (Sum.inr t0) : MMod F n) l'
      * rhoBasis (Fof u i : OspBasis F n) l' jout)
  rw [hsplit]
  have hz : (∑ t : I n, (rhoBasis (Fof v j : OspBasis F n) (Sum.inr t0) : MMod F n) (Sum.inr t)
        * rhoBasis (Fof u i : OspBasis F n) (Sum.inr t) jout) = 0 := by
    apply Finset.sum_eq_zero; intro t _
    have h1 : (rhoBasis (Fof v j : OspBasis F n) (Sum.inr t0) : MMod F n) (Sum.inr t) = 0 := by
      rw [rhoBasis_Fof_inr]; simp [eNM_inl_inr_eq_zero]
    rw [h1, zero_mul]
  rw [hz, add_zero]
  have hexp : (∑ b : F.K, (rhoBasis (Fof v j : OspBasis F n) (Sum.inr t0) : MMod F n) (Sum.inl b)
        * rhoBasis (Fof u i : OspBasis F n) (Sum.inl b) jout)
      = ∑ b : F.K, ((1/2:ℚ) * J n v t0 * (if b = j then (1:ℚ) else 0))
          * rhoBasis (Fof u i : OspBasis F n) (Sum.inl b) jout := by
    apply Finset.sum_congr rfl; intro b _
    rw [rhoBasis_Fof_inr]
    simp only [Pi.smul_apply, smul_eq_mul, eNM_K_eq]
    split_ifs <;> ring
  rw [hexp]
  have hfac : (∑ b : F.K, ((1/2:ℚ) * J n v t0 * (if b = j then (1:ℚ) else 0))
        * rhoBasis (Fof u i : OspBasis F n) (Sum.inl b) jout)
      = (1/2:ℚ) * J n v t0 * ∑ b : F.K, (if b = j then (1:ℚ) else 0)
          * rhoBasis (Fof u i : OspBasis F n) (Sum.inl b) jout := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; split_ifs <;> ring
  rw [hfac]
  have hc : (∑ b : F.K, (if b = j then (1:ℚ) else 0)
        * rhoBasis (Fof u i : OspBasis F n) (Sum.inl b) jout)
      = rhoBasis (Fof u i : OspBasis F n) (Sum.inl j) jout := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hc, rhoBasis_Fof_inl]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem bracket0BasisQ_F_F {F : FermionIndex} {n : ℕ} (u v : I n) (i j : F.K) (k' : OspBasis F n) :
    bracket0BasisQ (Fof u i : OspBasis F n) (Fof v j : OspBasis F n) k'
      = (1/4 * J n u v) * (MvPolynomial.constantCoeff (Sof i j k' : Pmn F n) : ℚ)
        + (1/2 * F.g i j) * (if k' = Lof u v then (1:ℚ) else 0) := by
  unfold bracket0BasisQ bracket0Basis bracketFF Fof
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [Algebra.smul_def, Algebra.smul_def, map_add, map_mul]
  rw [eN_eq_algebraMap]
  simp only [Algebra.algebraMap_eq_smul_one]
  split_ifs <;> simp

theorem rhoBasis_FF_rhs {F : FermionIndex} {n : ℕ} (u v : I n) (i j : F.K) (m : Midx F n) :
    (∑ k' : OspBasis F n, (bracket0BasisQ (Fof u i : OspBasis F n) (Fof v j : OspBasis F n) k')
        • rhoBasis k' m : MMod F n)
      = (1/4 * J n u v) • SofRho i j m + (1/2 * F.g i j) • rhoBasis (Lof u v : OspBasis F n) m := by
  have heq : (∑ k' : OspBasis F n,
        bracket0BasisQ (Fof u i : OspBasis F n) (Fof v j : OspBasis F n) k' • rhoBasis k' m)
      = ∑ k' : OspBasis F n,
        ((1/4 * J n u v) * (MvPolynomial.constantCoeff (Sof i j k' : Pmn F n) : ℚ)
          + (1/2 * F.g i j) * (if k' = Lof u v then (1:ℚ) else 0)) • rhoBasis k' m := by
    apply Finset.sum_congr rfl; intro k' _
    rw [bracket0BasisQ_F_F]
  rw [heq]
  rw [show (∑ k' : OspBasis F n,
        ((1/4 * J n u v) * (MvPolynomial.constantCoeff (Sof i j k' : Pmn F n) : ℚ)
          + (1/2 * F.g i j) * (if k' = Lof u v then (1:ℚ) else 0)) • rhoBasis k' m)
      = (∑ k' : OspBasis F n,
          ((1/4 * J n u v) * (MvPolynomial.constantCoeff (Sof i j k' : Pmn F n) : ℚ))
            • rhoBasis k' m)
        + (∑ k' : OspBasis F n,
          ((1/2 * F.g i j) * (if k' = Lof u v then (1:ℚ) else 0)) • rhoBasis k' m)
      from by rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k' _
              rw [add_smul]]
  congr 1
  · rw [show (∑ k' : OspBasis F n,
          ((1/4 * J n u v) * (MvPolynomial.constantCoeff (Sof i j k' : Pmn F n) : ℚ))
            • rhoBasis k' m)
        = (1/4 * J n u v) • (∑ k' : OspBasis F n,
            (MvPolynomial.constantCoeff (Sof i j k' : Pmn F n) : ℚ) • rhoBasis k' m)
        from by rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro k' _; rw [smul_smul]]
    rw [rho_sum_Sof]
  · rw [Finset.sum_eq_single (Lof u v : OspBasis F n)]
    · simp
    · intro k' _ hk'; simp [hk']
    · intro h; exact absurd (Finset.mem_univ _) h

/-- The `F,F` sector at `m = inl a`: the genuine computation lands in the `inl`
components (via `SofRho`'s own `inl`/`inl` formula); `J_antisymm` closes the sign
mismatch from swapping `(u,i) ↔ (v,j)`. -/
theorem rho_bracket_FF_inl {F : FermionIndex} {n : ℕ} (u v : I n) (i j a : F.K) :
    (rhoOp (Fof u i : OspBasis F n) (rhoBasis (Fof v j : OspBasis F n) (Sum.inl a))
        - gsign (parity (Fof u i : OspBasis F n)) (parity (Fof v j : OspBasis F n))
          • rhoOp (Fof v j : OspBasis F n) (rhoBasis (Fof u i : OspBasis F n) (Sum.inl a)))
      = ∑ k' : OspBasis F n, (bracket0BasisQ (Fof u i : OspBasis F n) (Fof v j : OspBasis F n) k')
          • rhoBasis k' (Sum.inl a) := by
  rw [show parity (Fof u i : OspBasis F n) = 1 from rfl,
    show parity (Fof v j : OspBasis F n) = 1 from rfl,
    show gsign (1 : ZMod 2) (1 : ZMod 2) = -1 from by decide, neg_smul, sub_neg_eq_add,
    one_smul, rhoBasis_FF_rhs]
  have hL0 : (rhoBasis (Lof u v : OspBasis F n) (Sum.inl a) : MMod F n) = 0 := by
    unfold Lof; split_ifs <;> unfold rhoBasis <;> rfl
  rw [hL0, smul_zero, add_zero]
  funext jout
  simp only [Pi.add_apply]
  rw [rhoOp_Fof_Fof_inl, rhoOp_Fof_Fof_inl]
  simp only [Pi.smul_apply, smul_eq_mul]
  match jout with
  | .inl a' =>
    rw [SofRho_inl_inl]
    simp only [eNM_K_eq]
    rw [J_antisymm v u]
    ring
  | .inr s =>
    rw [show (eNM (Sum.inl i) : MMod F n) (Sum.inr s) = 0 from by unfold eNM; simp,
        show (eNM (Sum.inl j) : MMod F n) (Sum.inr s) = 0 from by unfold eNM; simp,
        SofRho_inl_inr_zero]
    ring

/-- The `F,F` sector at `m = inr t0`: the genuine computation lands in the `inr`
components; `F.g_symm` closes the sign match from swapping `(u,i) ↔ (v,j)`. -/
theorem rho_bracket_FF_inr {F : FermionIndex} {n : ℕ} (u v : I n) (i j : F.K) (t0 : I n) :
    (rhoOp (Fof u i : OspBasis F n) (rhoBasis (Fof v j : OspBasis F n) (Sum.inr t0))
        - gsign (parity (Fof u i : OspBasis F n)) (parity (Fof v j : OspBasis F n))
          • rhoOp (Fof v j : OspBasis F n) (rhoBasis (Fof u i : OspBasis F n) (Sum.inr t0)))
      = ∑ k' : OspBasis F n, (bracket0BasisQ (Fof u i : OspBasis F n) (Fof v j : OspBasis F n) k')
          • rhoBasis k' (Sum.inr t0) := by
  rw [show parity (Fof u i : OspBasis F n) = 1 from rfl,
    show parity (Fof v j : OspBasis F n) = 1 from rfl,
    show gsign (1 : ZMod 2) (1 : ZMod 2) = -1 from by decide, neg_smul, sub_neg_eq_add,
    one_smul, rhoBasis_FF_rhs]
  rw [SofRho_inr_zero, smul_zero, zero_add]
  funext jout
  simp only [Pi.add_apply]
  rw [rhoOp_Fof_Fof_inr, rhoOp_Fof_Fof_inr]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [rhoBasis_Lof]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [F.g_symm j i]
  ring

/-- **The `F,F` sector of `rho_bracket`**, for arbitrary `m : Midx F n`. -/
theorem rho_bracket_FF {F : FermionIndex} {n : ℕ} (u v : I n) (i j : F.K) (m : Midx F n) :
    (rhoOp (Fof u i : OspBasis F n) (rhoBasis (Fof v j : OspBasis F n) m)
        - gsign (parity (Fof u i : OspBasis F n)) (parity (Fof v j : OspBasis F n))
          • rhoOp (Fof v j : OspBasis F n) (rhoBasis (Fof u i : OspBasis F n) m))
      = ∑ k' : OspBasis F n, (bracket0BasisQ (Fof u i : OspBasis F n) (Fof v j : OspBasis F n) k')
          • rhoBasis k' m := by
  match m with
  | .inl a => exact rho_bracket_FF_inl u v i j a
  | .inr t0 => exact rho_bracket_FF_inr u v i j t0

/-- `Lof u v`, with a canonical-order proof `huv` explicitly in hand, equals the raw
`Sum.inl` Sigma-type element directly -- proof irrelevance makes the two proofs of
`IKey u ≤ IKey v` interchangeable. Used to bridge `rho_bracket_LL`/`rho_bracket_LF`'s
own `Lof`-based statements to `rho_bracket`'s destructured-`X`/`Y` match. -/
theorem Lof_eq_sigma {F : FermionIndex} {n : ℕ} (u v : I n) (huv : IKey u ≤ IKey v) :
    (Lof u v : OspBasis F n) = Sum.inl ⟨(u, v), huv⟩ := by
  unfold Lof; rw [dite_eq_left huv]

/-- **`ρ` preserves brackets** (paper Prop. 3.4, part "Brackets"). All 6
genuine kind-pair sectors are proved outright above (`rho_bracket_LL`,
`rho_bracket_LS`, `rho_bracket_LF`, `rho_bracket_SS`, `rho_bracket_SF`,
`rho_bracket_FF`); the remaining 3 (`S,L`/`F,L`/`F,S`) derive from their own
reverse via `rho_bracket_reversal`. `rho_bracket_LS` is already stated directly on
the raw `Sum.inl` Sigma form (no `Lof`-bridging needed); `rho_bracket_LL`/
`rho_bracket_LF` need `Lof_eq_sigma` to bridge their own `Lof`-based statements to
the destructured `X`/`Y` here. -/
theorem rho_bracket {F : FermionIndex} {n : ℕ} (X Y : OspBasis F n) (i : Midx F n) :
    rhoOp X (rhoBasis Y i) - gsign (parity X) (parity Y) • rhoOp Y (rhoBasis X i)
      = ∑ k : OspBasis F n, (bracket0BasisQ X Y k) • rhoBasis k i := by
  match X, Y with
  | .inl ⟨(u, v), huv⟩, .inl ⟨(w, z), hwz⟩ =>
    rw [show (Sum.inl ⟨(u, v), huv⟩ : OspBasis F n) = Lof u v from (Lof_eq_sigma u v huv).symm,
      show (Sum.inl ⟨(w, z), hwz⟩ : OspBasis F n) = Lof w z from (Lof_eq_sigma w z hwz).symm]
    exact rho_bracket_LL u v w z i
  | .inl ⟨(u, v), huv⟩, .inr (.inl ⟨(i0, j0), hij⟩) =>
    exact rho_bracket_LS u v huv i0 j0 hij i
  | .inl ⟨(u, v), huv⟩, .inr (.inr (w, j0)) =>
    rw [show (Sum.inl ⟨(u, v), huv⟩ : OspBasis F n) = Lof u v from (Lof_eq_sigma u v huv).symm]
    exact rho_bracket_LF u v w huv j0 i
  | .inr (.inl ⟨(i0, j0), hij⟩), .inl ⟨(u, v), huv⟩ =>
    exact rho_bracket_reversal (Sum.inl ⟨(u, v), huv⟩ : OspBasis F n)
      (Sum.inr (Sum.inl ⟨(i0, j0), hij⟩)) i (rho_bracket_LS u v huv i0 j0 hij i)
  | .inr (.inl ⟨(i0, j0), hij⟩), .inr (.inl ⟨(k0, l0), hkl⟩) =>
    exact rho_bracket_SS i0 j0 k0 l0 hij hkl i
  | .inr (.inl ⟨(j0, k0), hjk⟩), .inr (.inr (w, i0)) =>
    exact rho_bracket_SF j0 k0 hjk w i0 i
  | .inr (.inr (w, i0)), .inl ⟨(u, v), huv⟩ =>
    rw [show (Sum.inl ⟨(u, v), huv⟩ : OspBasis F n) = Lof u v from (Lof_eq_sigma u v huv).symm]
    exact rho_bracket_reversal (Lof u v) (Fof w i0) i (rho_bracket_LF u v w huv i0 i)
  | .inr (.inr (w, i0)), .inr (.inl ⟨(j0, k0), hjk⟩) =>
    exact rho_bracket_reversal (Sum.inr (Sum.inl ⟨(j0, k0), hjk⟩) : OspBasis F n) (Fof w i0) i
      (rho_bracket_SF j0 k0 hjk w i0 i)
  | .inr (.inr (u, i0)), .inr (.inr (v, j0)) =>
    exact rho_bracket_FF u v i0 j0 i

end OspN
end OspOddDeformations
