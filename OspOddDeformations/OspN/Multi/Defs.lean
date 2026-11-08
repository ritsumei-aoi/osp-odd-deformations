import OspOddDeformations.OspN.Kappa

/-!
# Multiple odd parameters: definitions (the statements are proved in later modules)

Paper Section 5: `R_r = P_r ⊗ Λ(κ_1,…,κ_r)`; the deformed bracket
`[X,Y]_β = [X,Y]_0 + Σ_s κ_s Γ^{(s)}(X,Y)` ((5.3), taken here as the definition); the change of
lifts `U` of Prop 5.2, for **any** even `Θ` with `ΘJΘᵀ = J − Ω`; Thm 5.3's identity
`[U X, U Y]_0 = U [X,Y]_β` for all `X,Y ∈ 𝔤_R`.

Design choices:
* The even parameters `β^{(s)}_{u,i}` are the variables `X (s,u,i)` of `PmnR F n r`. The
  single-parameter `Γ_β` (`GammaBasis`, over `Pmn F n`) is transported by `rename (s, ·)`, so
  `Γ^{(s)}` reuses the proved `Γ_β` rather than restating it.
* The base bracket's coefficients are rational constants; they are carried to `PmnR` by
  `aeval 0` (exact on constants).
* The Grassmann part is the index `Finset (Fin r)` of a basis `OspBasis F n × Finset (Fin r)`,
  with `κ_S κ_T = gs S T κ_{S ∪ T}`. Coefficients in `PmnR` are even and commute.
* Sums over `K_N` carry the dual index on the coefficient, as in the paper.
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

/-! ## Coefficients -/

/-- `P_r`: polynomials in the `β^{(s)}_{u,i}`, `s < r`. -/
noncomputable abbrev PmnR (F : FermionIndex) (n r : ℕ) : Type :=
  MvPolynomial (Fin r × I n × F.K) ℚ

/-- `β^{(s)}_{u,i}`. -/
noncomputable def betaR (F : FermionIndex) (n r : ℕ) (s : Fin r) (u : I n) (i : F.K) :
    PmnR F n r :=
  MvPolynomial.X (s, u, i)

/-- The single-parameter coefficient ring into `P_r`, at the parameter `s`:
`β_{u,i} ↦ β^{(s)}_{u,i}`. -/
noncomputable def embS (s : Fin r) : Pmn F n →ₐ[ℚ] PmnR F n r :=
  MvPolynomial.rename (fun p => (s, p))

/-- Constants of `Pmn` into `P_r` (used for the base bracket, whose coefficients are rational). -/
noncomputable def emb0 : Pmn F n →ₐ[ℚ] PmnR F n r :=
  MvPolynomial.aeval (fun _ => 0)

/-- The sign of `κ_S κ_T = gs S T • κ_{S ∪ T}`: zero unless disjoint; otherwise `(-1)` to the
number of inversions `t < s` with `s ∈ S`, `t ∈ T`. -/
def gs (S T : Finset (Fin r)) : ℚ :=
  if Disjoint S T then (-1) ^ ((S ×ˢ T).filter (fun p => p.2 < p.1)).card else 0

/-! ## `𝔤_{R_r}` -/

abbrev RBasisM (F : FermionIndex) (n r : ℕ) : Type := OspBasis F n × Finset (Fin r)

noncomputable abbrev RModM (F : FermionIndex) (n r : ℕ) : Type := RBasisM F n r → PmnR F n r

/-- `κ_S ⊗ v`, for `v` a `𝔤`-valued element with coefficients in `P_r`. -/
noncomputable def kap (S : Finset (Fin r)) (v : OspBasis F n → PmnR F n r) : RModM F n r :=
  fun p => if p.2 = S then v p.1 else 0

/-- A `𝔤_P` element carried to `P_r` by a ring map. -/
noncomputable def liftBy (φ : Pmn F n →ₐ[ℚ] PmnR F n r) (x : OspMod F n) :
    OspBasis F n → PmnR F n r :=
  fun k => φ (x k)

/-- `[κ_S X, κ_T Y]_0 = (-1)^{|T| p(X)} κ_S κ_T [X,Y]_0` on basis elements. -/
noncomputable def bracket0MBasis (p q : RBasisM F n r) : RModM F n r :=
  ((-1 : ℚ) ^ (q.2.card * (parity p.1).val) * gs p.2 q.2) •
    kap (p.2 ∪ q.2) (liftBy emb0 (bracket0Basis p.1 q.1))

noncomputable def bracket0M (x y : RModM F n r) : RModM F n r :=
  ∑ p : RBasisM F n r, ∑ q : RBasisM F n r, (x p * y q) • bracket0MBasis p q

/-- `Γ^{(s)}` on basis elements: `Γ_β` with `β ↦ β^{(s)}`. -/
noncomputable def GammaSBasis (s : Fin r) (X Y : OspBasis F n) : OspBasis F n → PmnR F n r :=
  liftBy (embS s) (GammaBasis X Y)

/-- The deformed bracket (5.3) on basis elements:
`[κ_S X, κ_T Y]_β = (-1)^{|T| p(X)} κ_S κ_T ([X,Y]_0 + Σ_s κ_s Γ^{(s)}(X,Y))`. -/
noncomputable def bracketBetaMBasis (p q : RBasisM F n r) : RModM F n r :=
  bracket0MBasis p q +
    ∑ s : Fin r,
      ((-1 : ℚ) ^ (q.2.card * (parity p.1).val) * gs p.2 q.2 * gs (p.2 ∪ q.2) {s}) •
        kap (p.2 ∪ q.2 ∪ {s}) (GammaSBasis s p.1 q.1)

noncomputable def bracketBetaM (x y : RModM F n r) : RModM F n r :=
  ∑ p : RBasisM F n r, ∑ q : RBasisM F n r, (x p * y q) • bracketBetaMBasis p q

/-! ## The Grassmann algebra `R_r` and the matrices -/

/-- Elements of `R_r`, as `Finset (Fin r) → P_r`. -/
noncomputable abbrev GR (F : FermionIndex) (n r : ℕ) : Type := Finset (Fin r) → PmnR F n r

noncomputable def gmul (a b : GR F n r) : GR F n r :=
  fun T => ∑ A : Finset (Fin r), ∑ B : Finset (Fin r),
    if A ∪ B = T then gs A B • (a A * b B) else 0

noncomputable def gone : GR F n r := fun T => if T = ∅ then 1 else 0

/-- `r • κ_S`-style scalars: the element with the single component `c` at `S`. -/
noncomputable def gmono (S : Finset (Fin r)) (c : PmnR F n r) : GR F n r :=
  fun T => if T = S then c else 0

/-- Even: supported on sets of even cardinality. -/
def IsEvenGR (a : GR F n r) : Prop := ∀ T, T.card % 2 = 1 → a T = 0

/-- `γ_{u,i} = Σ_s β^{(s)}_{u,i} κ_s`. -/
noncomputable def gammaR (u : I n) (i : F.K) : GR F n r :=
  ∑ s : Fin r, gmono {s} (betaR F n r s u i)

/-- `Ω_{uv} = -Σ_i γ_{u,i} γ_{v,i*}`. -/
noncomputable def OmegaR (u v : I n) : GR F n r :=
  -∑ i : F.K, gmul (gammaR u i) (gammaR v (F.dual i))

/-- `J` as an `R_r`-valued matrix. -/
noncomputable def JR (u v : I n) : GR F n r :=
  fun T => if T = ∅ then MvPolynomial.C (J n u v) else 0

/-- `(Θ J Θᵀ)_{uv}`. -/
noncomputable def thetaJthetaT (Θ : I n → I n → GR F n r) (u v : I n) : GR F n r :=
  ∑ w : I n, ∑ z : I n, gmul (Θ u w) (gmul (JR w z) (Θ v z))

/-- A left `R_r`-action on `𝔤_{R_r}`: `a • w`, with `a` on the left. -/
noncomputable def gsmul (a : GR F n r) (w : RModM F n r) : RModM F n r :=
  fun p => ∑ A : Finset (Fin r), ∑ B : Finset (Fin r),
    if A ∪ B = p.2 then gs A B • (a A * w (p.1, B)) else 0

/-- `a ⊗ Z` for `a ∈ R_r` and a basis symbol `Z` (with coefficient `1`). -/
noncomputable def gtens (a : GR F n r) (v : OspMod F n) : RModM F n r :=
  fun p => a p.2 * emb0 (v p.1)

/-! ## The change of lifts `U` (Prop 5.2, dual index on the coefficient) -/

/-- `U` on the basis symbols with `S = ∅`. -/
noncomputable def UBasis0 (Θ : I n → I n → GR F n r) : OspBasis F n → RModM F n r
  | .inl ⟨(u, v), _⟩ =>
      (∑ w : I n, ∑ z : I n, gtens (gmul (Θ u w) (Θ v z)) (eN (Lof w z)))
      + ∑ w : I n, ∑ i : F.K,
          gtens (gmul (Θ u w) (gammaR v (F.dual i)) + gmul (Θ v w) (gammaR u (F.dual i)))
            (eN (Fof w i))
      - (1 / 2 : ℚ) • ∑ i : F.K, ∑ j : F.K,
          gtens (gmul (gammaR u (F.dual i)) (gammaR v (F.dual j))) (Sof i j)
  | .inr (.inl ⟨(i, j), _⟩) => gtens gone (Sof i j)
  | .inr (.inr (u, i)) =>
      (∑ w : I n, gtens (Θ u w) (eN (Fof w i)))
      + (1 / 2 : ℚ) • ∑ j : F.K, gtens (gammaR u (F.dual j)) (Sof j i)

/-- `U`, even and `R_r`-linear: `U (κ_S X) = κ_S U X`. -/
noncomputable def UM (Θ : I n → I n → GR F n r) (x : RModM F n r) : RModM F n r :=
  ∑ p : RBasisM F n r, x p • gsmul (gmono p.2 1) (UBasis0 Θ p.1)


/-- `Θ = 𝕀 + ½ ΩJ`. -/
noncomputable def thetaHalf (u w : I n) : GR F n r :=
  (if u = w then gone else 0) + (1 / 2 : ℚ) • ∑ z : I n, gmul (OmegaR u z) (JR z w)

/-- `Bool ≃ Finset (Fin 1)`: `false ↦ ∅`, `true ↦ {0}`. -/
def toS1 : Bool → Finset (Fin 1)
  | false => ∅
  | true => {0}

/-- `Kappa.lean`'s `𝔤_R` (`r = 1`) inside `𝔤_{R_1}`: `(k, b) ↦ (k, toS1 b)`, coefficients by
`embS 0`. -/
noncomputable def ofR1 (x : RMod F n) : RModM F n 1 :=
  fun p => if p.2 = ∅ then embS 0 (x (p.1, false)) else embS 0 (x (p.1, true))

end Multi
end OspN
end OspOddDeformations
