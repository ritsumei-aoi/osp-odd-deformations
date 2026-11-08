import OspOddDeformations.OspN.Presented.MultiUntwist
import OspOddDeformations.OspN.Presented.Base
import OspOddDeformations.OspN.Multi.Conjugation

/-!
# The lifts over `R_r`

For the paper's instance `A_β = SrcM (jR F n r) (gR F n r) β'` (`β' = betaR` or `0`):

* `κS S = κ_{s_1} ⋯ κ_{s_k}` for `S = {s_1 < ⋯ < s_k}`, and `embG a = Σ_S a_S κ_S`, which
  carries the Grassmann model `GR F n r` of `R_r` (`Multi/Defs.lean`) into `A_β`;
* the lifts `XpM` (eq. (2.2)), and `ι` over `R_r`: `iotaM x = Σ_{X,S} x(X,S) κ_S X̂`, on the
  coordinate-level `𝔤_{R_r} = RModM F n r`;
* `eM X`, the basis element `X` of `𝔤` in `RModM`.

The statements built on these are proved in:
* `MultiRealize.lean`: `κ_S κ_T = gs S T κ_{S∪T}` and `embG` multiplicative; `embG`
  carries the coordinate-level `γ`, `Ω` and `Θ` to those of `MultiDefs` and `MultiUntwist`;
  **Prop 3.3 over `R_r`** (`iotaM_zero_injective`);
* `MultiLiftChange.lean`: **Prop 5.2**, `Φ_r(ι_β X) = ι_0(U X)` with the coordinate-level `U` at
  its `Θ`;
* `MultiRecovery.lean`: **Thm 5.3** in `A_β`: `[ι_β X, ι_β Y] = ι_β([X,Y]_β)` with the
  coordinate-level `[·,·]_β` (eq. (5.3)), `ι_β` injective, and `[X,Y]_β` the unique such element.
-/

namespace OspOddDeformations
namespace OspN
namespace Presented

open Bmn (I J)

variable (F : FermionIndex) (n r : ℕ)

/-- `A_β` over `R_r`, the paper's instance. -/
abbrev AM (β' : Fin r → I n → F.K → Multi.PmnR F n r) : Type := SrcM (jR F n r) (gR F n r) β'

noncomputable instance (β' : Fin r → I n → F.K → Multi.PmnR F n r) : Algebra ℚ (AM F n r β') :=
  inferInstanceAs (Algebra ℚ (RingQuot _))

instance (β' : Fin r → I n → F.K → Multi.PmnR F n r) :
    IsScalarTower ℚ (Multi.PmnR F n r) (AM F n r β') :=
  inferInstanceAs (IsScalarTower ℚ (Multi.PmnR F n r) (RingQuot _))

variable {F n r}
variable (β' : Fin r → I n → F.K → Multi.PmnR F n r)

/-- `κ_S`, the ordered product. -/
noncomputable def κS (S : Finset (Fin r)) : AM F n r β' :=
  ((S.sort (· ≤ ·)).map (κM _ _ β')).prod

/-- `R_r` (the coordinate-level `GR`) into `A_β`: `a ↦ Σ_S a_S κ_S`. -/
noncomputable def embG (a : Multi.GR F n r) : AM F n r β' := ∑ S, a S • κS β' S

/-- `L̂_{uv} = ¼(b_u b_v + b_v b_u)`. -/
noncomputable def LpM (u v : I n) : AM F n r β' :=
  (1 / 4 : ℚ) • (bM _ _ β' u * bM _ _ β' v + bM _ _ β' v * bM _ _ β' u)
/-- `Ŝ_{ij} = ½(a_i a_j − a_j a_i)`. -/
noncomputable def SpM (i j : F.K) : AM F n r β' :=
  (1 / 2 : ℚ) • (aM _ _ β' i * aM _ _ β' j - aM _ _ β' j * aM _ _ β' i)
/-- `F̂_{u,i} = ¼(a_i b_u + b_u a_i)`. -/
noncomputable def FpM (u : I n) (i : F.K) : AM F n r β' :=
  (1 / 4 : ℚ) • (aM _ _ β' i * bM _ _ β' u + bM _ _ β' u * aM _ _ β' i)

/-- The lift of a basis element. -/
noncomputable def XpM : OspBasis F n → AM F n r β'
  | .inl ⟨(u, v), _⟩ => LpM β' u v
  | .inr (.inl ⟨(i, j), _⟩) => SpM β' i j
  | .inr (.inr (u, i)) => FpM β' u i

/-- `ι` over `R_r`: `x ↦ Σ_{X,S} x(X,S) κ_S X̂`. -/
noncomputable def iotaM (x : Multi.RModM F n r) : AM F n r β' :=
  ∑ p : Multi.RBasisM F n r, x p • (κS β' p.2 * XpM β' p.1)

/-- The basis element `X` of `𝔤`, in `𝔤_{R_r}`. -/
noncomputable def eM (X : OspBasis F n) : Multi.RModM F n r :=
  Multi.kap ∅ (Multi.liftBy Multi.emb0 (eN X))

end Presented
end OspN
end OspOddDeformations
