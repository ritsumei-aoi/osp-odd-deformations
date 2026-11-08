import OspOddDeformations.OspN.Multi.Defs

/-!
# The factorization `U = Θ_* ∘ V_γ` (paper Prop 5.4)

Definitions and statements.

Definitions (`GR`-coefficients, extended `R_r`-linearly on the left as `UM` is):
* `ThetaStar Θ` — `Θ_*`, Prop 5.4;
* `VChi χ` — `V_χ`, Prop 5.4's display, for any family `χ` of elements of `GR` (odd in use);
* `bracketJM J'` — the bracket `[·,·]_{J'}` of Lemma 3.2 (eqs. (3.1)–(3.6)) with `J'` in
  place of `J`, extended `R_r`-super-bilinearly with the sign of `bracket0M`.

Statements (proved in `Multi/Factorization.lean`, `Multi/ThetaStarBracket.lean`,
`Multi/VChiBracket.lean`; no `sorry`): `UM Θ = Θ_* ∘ V_γ`,
(i) `[Θ_*X, Θ_*Y]_0 = Θ_*[X,Y]_{J-Ω}`, (ii) `[V_γX, V_γY]_{J-Ω} = V_γ[X,Y]_β`.
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

/-! ## `Θ_*` -/

/-- `Θ_*` on the basis symbols (Prop 5.4): `Θ_*(S_{ij}) = S_{ij}`,
`Θ_*(L_{uv}) = Σ_{w,z} Θ_{uw}Θ_{vz} L_{wz}`, `Θ_*(F_{u,i}) = Σ_w Θ_{uw} F_{w,i}`. -/
noncomputable def ThetaStarBasis0 (Θ : I n → I n → GR F n r) : OspBasis F n → RModM F n r
  | .inl ⟨(u, v), _⟩ => ∑ w : I n, ∑ z : I n, gtens (gmul (Θ u w) (Θ v z)) (eN (Lof w z))
  | .inr (.inl ⟨(i, j), _⟩) => gtens gone (Sof i j)
  | .inr (.inr (u, i)) => ∑ w : I n, gtens (Θ u w) (eN (Fof w i))

/-- `Θ_*`, even and `R_r`-linear: `Θ_*(κ_S X) = κ_S Θ_* X`. -/
noncomputable def ThetaStar (Θ : I n → I n → GR F n r) (x : RModM F n r) : RModM F n r :=
  ∑ p : RBasisM F n r, x p • gsmul (gmono p.2 1) (ThetaStarBasis0 Θ p.1)

/-! ## `V_χ` -/

/-- `V_χ` on the basis symbols (Prop 5.4's display; the dual index on the coefficient):
`V_χ(S_{ij}) = S_{ij}`,
`V_χ(L_{uv}) = L_{uv} + Σ_i (χ_{v,i*} F_{u,i} + χ_{u,i*} F_{v,i})`
`  - ½ Σ_{i,j} χ_{u,i*}χ_{v,j*} S_{ij}`,
`V_χ(F_{u,i}) = F_{u,i} + ½ Σ_j χ_{u,j*} S_{ji}`. -/
noncomputable def VBasis0 (χ : I n → F.K → GR F n r) : OspBasis F n → RModM F n r
  | .inl ⟨(u, v), _⟩ =>
      gtens gone (eN (Lof u v))
      + ∑ i : F.K, (gtens (χ v (F.dual i)) (eN (Fof u i)) + gtens (χ u (F.dual i)) (eN (Fof v i)))
      - (1 / 2 : ℚ) • ∑ i : F.K, ∑ j : F.K,
          gtens (gmul (χ u (F.dual i)) (χ v (F.dual j))) (Sof i j)
  | .inr (.inl ⟨(i, j), _⟩) => gtens gone (Sof i j)
  | .inr (.inr (u, i)) =>
      gtens gone (eN (Fof u i)) + (1 / 2 : ℚ) • ∑ j : F.K, gtens (χ u (F.dual j)) (Sof j i)

/-- `V_χ`, even and `R_r`-linear: `V_χ(κ_S X) = κ_S V_χ X`. -/
noncomputable def VChi (χ : I n → F.K → GR F n r) (x : RModM F n r) : RModM F n r :=
  ∑ p : RBasisM F n r, x p • gsmul (gmono p.2 1) (VBasis0 χ p.1)

/-! ## `[·,·]_{J'}` -/

/-- Lemma 3.2's bracket with `J'` (an `R_r`-valued matrix) in place of `J`, on basis symbols
(`κ`-degree `0`): the formulas of `bracket0Basis` (`bracketLL`, …, `bracketFF`) with `J n a b`
replaced by `J' a b`. -/
noncomputable def bracketJBasis0 (J' : I n → I n → GR F n r) :
    OspBasis F n → OspBasis F n → RModM F n r
  | .inl ⟨(u, v), _⟩, .inl ⟨(w, z), _⟩ =>
      (1 / 2 : ℚ) • (gtens (J' v w) (eN (Lof u z)) + gtens (J' u w) (eN (Lof v z))
        + gtens (J' v z) (eN (Lof u w)) + gtens (J' u z) (eN (Lof v w)))
  | .inl _, .inr (.inl _) => 0
  | .inl ⟨(u, v), _⟩, .inr (.inr (w, i)) =>
      (1 / 2 : ℚ) • (gtens (J' v w) (eN (Fof u i)) + gtens (J' u w) (eN (Fof v i)))
  | .inr (.inl _), .inl _ => 0
  | .inr (.inl ⟨(i, j), _⟩), .inr (.inl ⟨(k, l), _⟩) => gtens gone (bracketSS i j k l)
  | .inr (.inl ⟨(j, k), _⟩), .inr (.inr (w, i)) => gtens gone (bracketSF j k w i)
  | .inr (.inr (w, i)), .inl ⟨(u, v), _⟩ =>
      -((1 / 2 : ℚ) • (gtens (J' v w) (eN (Fof u i)) + gtens (J' u w) (eN (Fof v i))))
  | .inr (.inr (w, i)), .inr (.inl ⟨(j, k), _⟩) => -gtens gone (bracketSF j k w i)
  | .inr (.inr (u, i)), .inr (.inr (v, j)) =>
      (1 / 4 : ℚ) • gtens (J' u v) (Sof i j) + (1 / 2 * F.g i j) • gtens gone (eN (Lof u v))

/-- `[·,·]_{J'}`, `R_r`-super-bilinear: `[κ_S X, κ_T Y]_{J'} = (-1)^{|T| p(X)} κ_S κ_T [X,Y]_{J'}`
(the sign convention of `bracket0M`). -/
noncomputable def bracketJM (J' : I n → I n → GR F n r) (x y : RModM F n r) : RModM F n r :=
  ∑ p : RBasisM F n r, ∑ q : RBasisM F n r,
    (x p * y q) • (((-1 : ℚ) ^ (q.2.card * (parity p.1).val)) •
      gsmul (gmono p.2 1) (gsmul (gmono q.2 1) (bracketJBasis0 J' p.1 q.1)))

/-- `J - Ω`, the bilinear form of Prop 5.4. -/
noncomputable def JmOmega (u v : I n) : GR F n r := JR u v - OmegaR u v

end Multi
end OspN
end OspOddDeformations
