import OspOddDeformations.OspN.Multi.Factor
import OspOddDeformations.OspN.Multi.Sigma
import OspOddDeformations.OspN.Multi.TierBLemmas
import OspOddDeformations.OspN.Multi.TierBAut

/-!
# The rest of Prop 5.4

Paper Prop 5.4. `U = Θ_*∘V_γ` (`UM_eq_comp`) and both intertwinings (`thetaStar_bracket`,
`vChi_bracket`) are proved in `Multi/Factorization.lean`, `Multi/ThetaStarBracket.lean` and
`Multi/VChiBracket.lean`. Proved here:
* `V_χ V_ψ = V_{χ+ψ}` for odd families `χ, ψ`. So the `T^{(s)} = V_{β^{(s)}κ_s}` commute, and
  `T^{(1)}⋯T^{(r)} = V_γ`;
* `Π_* (Π')_* = (Π'Π)_*` for even matrices `Π, Π'` (`ThetaStar_comp`, with `Π = M'`, `Π' = M`);
* Prop 5.4 in full: `U = Θ_* ∘ T^{(1)} ⋯ T^{(r)}`;
* if `Ω ≠ 0`, then `Θ_*` is not an automorphism of `[·,·]_0`.
The Lie laws of `[·,·]_{J'}` are not needed.
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

/-- An odd family: every entry is supported on sets of odd cardinality. -/
def IsOddFamily (χ : I n → F.K → GR F n r) : Prop := ∀ u i, HasParity 1 (χ u i)

/-- An even matrix: every entry is supported on sets of even cardinality. -/
def IsEvenMatrix (M : I n → I n → GR F n r) : Prop := ∀ u w, IsEvenGR (M u w)

/-- The matrix product over `R_r`: `(M M')_{uz} = Σ_w M_{uw} M'_{wz}`. -/
noncomputable def mmul (M M' : I n → I n → GR F n r) (u z : I n) : GR F n r :=
  ∑ w : I n, gmul (M u w) (M' w z)

/-- `β^{(s)}κ_s`, the odd family of the single parameter `s`. -/
noncomputable def chiS (s : Fin r) (u : I n) (i : F.K) : GR F n r :=
  gmono {s} (betaR F n r s u i)

/-- `T^{(s)} = V_{β^{(s)}κ_s}`. -/
noncomputable def TS (s : Fin r) : RModM F n r → RModM F n r := VChi (chiS s)

/-- `T^{(1)} ∘ ⋯ ∘ T^{(r)}`. -/
noncomputable def TProd : RModM F n r → RModM F n r :=
  (List.finRange r).foldr (fun s f => TS s ∘ f) id

/-! ## `V_χ` -/

/-- **Prop 5.4**: `V_χ V_ψ = V_{χ+ψ}` for odd `χ, ψ`. -/
theorem VChi_comp (χ ψ : I n → F.K → GR F n r) (hχ : IsOddFamily χ) (hψ : IsOddFamily ψ)
    (x : RModM F n r) :
    VChi χ (VChi ψ x) = VChi (χ + ψ) x := by
  exact VChi_comp' χ ψ hχ hψ x

/-- The `T^{(s)}` commute. -/
theorem TS_comm (s t : Fin r) (x : RModM F n r) : TS s (TS t x) = TS t (TS s x) := by
  have hs : IsOddFamily (chiS (F := F) (n := n) (r := r) s) := fun u i =>
    HasParity_gmono_singleton s _
  have ht : IsOddFamily (chiS (F := F) (n := n) (r := r) t) := fun u i =>
    HasParity_gmono_singleton t _
  unfold TS
  rw [VChi_comp _ _ hs ht, VChi_comp _ _ ht hs, add_comm]

/-- `T^{(1)} ⋯ T^{(r)} = V_γ`. -/
theorem TProd_eq (x : RModM F n r) : TProd x = VChi gammaR x := by
  have hf : ∀ (s : Fin r) (u : I n) (i : F.K), HasParity 1 (chiS (F := F) s u i) := fun s u i =>
    HasParity_gmono_singleton s _
  unfold TProd
  have := foldr_VChi (F := F) (n := n) chiS hf (List.finRange r) x
  refine this.trans ?_
  congr 1

/-! ## `Π_*` (`ThetaStar`) -/

/-- **Prop 5.4**: `Π_* (Π')_* = (Π'Π)_*` for even `Π, Π'`; here `Π = M'` and `Π' = M`. -/
theorem ThetaStar_comp (M M' : I n → I n → GR F n r) (hM : IsEvenMatrix M)
    (hM' : IsEvenMatrix M') (x : RModM F n r) :
    ThetaStar M' (ThetaStar M x) = ThetaStar (mmul M M') x := by
  rw [ThetaStar_eq_linM, ThetaStar_eq_linM, ThetaStar_eq_linM, linM_comp]
  congr 1
  funext Z
  exact TSB0_comp M M' hM hM' Z

/-! ## Prop 5.4 in full, and the failure of `Θ_*` alone -/

/-- **Prop 5.4**: `U = Θ_* ∘ T^{(1)} ⋯ T^{(r)}`, for even `Θ`. -/
theorem UM_eq_ThetaStar_TProd (Θ : I n → I n → GR F n r) (hEven : IsEvenMatrix Θ)
    (x : RModM F n r) :
    UM Θ x = ThetaStar Θ (TProd x) := by
  rw [TProd_eq]
  exact UM_eq_comp' Θ hEven x

/-- If `Ω ≠ 0`, then `Θ_*` is not an automorphism of `[·,·]_0` (Prop 5.4, last sentence; the
witness here is `[L_{uu}, F_{w,i}]`). -/
theorem ThetaStar_not_aut (Θ : I n → I n → GR F n r) (hEven : IsEvenMatrix Θ)
    (hΘ : ∀ u v, thetaJthetaT Θ u v = JR u v - OmegaR u v)
    (hΩ : ∃ u v : I n, OmegaR (F := F) (r := r) u v ≠ 0) :
    ¬ ∀ x y : RModM F n r,
      bracket0M (ThetaStar Θ x) (ThetaStar Θ y) = ThetaStar Θ (bracket0M x y) := by
  intro hall
  obtain ⟨u, w, hΩ'⟩ := hΩ
  have hK : Nonempty F.K := by
    by_contra hK
    rw [not_nonempty_iff] at hK
    exact hΩ' (by simp [OmegaR])
  obtain ⟨i⟩ := hK
  have h1 := hall (gtens gone (eN (Lof u u : OspBasis F n))) (gtens gone (eN (Fof w i)))
  rw [thetaStar_bracket Θ hEven hΘ] at h1
  have hsub : ∀ P Q : RModM F n r, ThetaStar Θ (P - Q) = ThetaStar Θ P - ThetaStar Θ Q := by
    intro P Q; rw [ThetaStar_eq_linM]; exact linM_sub _ _ _
  have h2 : ThetaStar Θ (gtens (OmegaR u w) (eN (Fof u i))) = 0 := by
    have h3 := hsub (bracketJM JmOmega (gtens gone (eN (Lof u u : OspBasis F n)))
      (gtens gone (eN (Fof w i)))) (bracket0M (gtens gone (eN (Lof u u : OspBasis F n)))
      (gtens gone (eN (Fof w i))))
    rw [h1, sub_self, witness_diff, ThetaStar_eq_linM, linM_neg, neg_eq_zero] at h3
    rw [ThetaStar_eq_linM]
    exact h3
  obtain ⟨T, hT⟩ : ∃ T, OmegaR (F := F) (r := r) u w T ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hΩ' (funext hcon)
  have hcard : T.card = 2 := by
    by_contra hc
    exact hT (HasCard_OmegaR u w T hc)
  obtain ⟨a, ha⟩ := exists_theta_empty_ne Θ hΘ u
  have h4 := congrFun (gmul_theta_eq_zero_of_ThetaStar Θ _ u i h2 a) T
  rw [gmul_top_apply _ _ T 2 hcard (HasCard_OmegaR u w)] at h4
  exact mul_ne_zero hT ha h4

end Multi
end OspN
end OspOddDeformations
