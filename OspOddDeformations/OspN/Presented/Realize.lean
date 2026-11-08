import OspOddDeformations.OspN.Presented.Untwist
import OspOddDeformations.OspN.IndependenceR
import OspOddDeformations.OspN.FBeta

/-!
# The lifts in the presented algebras, the map to the realization, and Prop 3.3

The lifts (eq. (2.2)) are defined in `Src (jP F n) (gP F n) β'` for any `β'`: at `β' = beta F n`
they are the `X̂` of `A_β`, at `β' = 0` the `X^0` of `A_0`. `ι` sends `x ∈ 𝔤_P` to `Σ_X x_X X̂`.

`rho : AZero F n →+* AB F n` sends `B_u`, `a_i`, `κ` to the realization's `BuAB`, `aAB`, `kappaAB`
and is `P`-linear through `coefAB`. It is defined by the universal property, on the subalgebra
`SAB F n` that the realization's generators span, where `coefAB` is central. It sends the presented
lifts to the realization's (`rho_Xp`, `rho_iotaP`). Since the realization's `ι_0` is injective
(`iota0_injective`, `kappa_iota0_injective`), so is the presented one: **Prop 3.3** for `A_0`
(`iotaRP_injective`). No faithfulness of the realization is used.
-/

namespace OspOddDeformations
namespace OspN
namespace Presented

variable (F : FermionIndex) (n : ℕ)

/-! ## The lifts -/

/-- `1/4` and `1/2` in `P`. -/
noncomputable def q4 : Pmn F n := algebraMap ℚ (Pmn F n) (1 / 4)
/-- `1/2` in `P`. -/
noncomputable def q2 : Pmn F n := algebraMap ℚ (Pmn F n) (1 / 2)

variable {F n}
variable (β' : Bmn.I n → F.K → Pmn F n)

/-- `L̂_{uv} = ¼(b_u b_v + b_v b_u)`. -/
noncomputable def Lp (u v : Bmn.I n) : Src (jP F n) (gP F n) β' :=
  q4 F n • (b _ _ β' u * b _ _ β' v + b _ _ β' v * b _ _ β' u)
/-- `Ŝ_{ij} = ½(a_i a_j − a_j a_i)`. -/
noncomputable def Sp (i j : F.K) : Src (jP F n) (gP F n) β' :=
  q2 F n • (a _ _ β' i * a _ _ β' j - a _ _ β' j * a _ _ β' i)
/-- `F̂_{u,i} = ¼(a_i b_u + b_u a_i)`. -/
noncomputable def Fp (u : Bmn.I n) (i : F.K) : Src (jP F n) (gP F n) β' :=
  q4 F n • (a _ _ β' i * b _ _ β' u + b _ _ β' u * a _ _ β' i)

/-- The lift of a basis element. -/
noncomputable def Xp : OspBasis F n → Src (jP F n) (gP F n) β'
  | .inl ⟨(u, v), _⟩ => Lp β' u v
  | .inr (.inl ⟨(i, j), _⟩) => Sp β' i j
  | .inr (.inr (u, i)) => Fp β' u i

/-- `ι : 𝔤_P → Src`, `x ↦ Σ_X x_X X̂`. -/
noncomputable def iotaP (x : OspMod F n) : Src (jP F n) (gP F n) β' := ∑ X, x X • Xp β' X

/-- `ι` on `𝔤_R`: `x_0 + κx_1 ↦ ι(x_0) + κ ι(x_1)`. -/
noncomputable def iotaRP (x : RMod F n) : Src (jP F n) (gP F n) β' :=
  iotaP β' (falsePart x) + κ _ _ β' * iotaP β' (truePart x)

/-! ## The realization as a `P`-algebra, and `rho` -/

variable (F n)

/-- `coefAB` as a ring homomorphism. -/
noncomputable def coefHom : Pmn F n →+* AB F n :=
  (GradedTensorProduct.includeLeftRingHom (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)).comp
    (algebraMap (Pmn F n) (R F n))

theorem coefHom_apply (c : Pmn F n) : coefHom F n c = coefAB F n c := rfl

theorem coefAB_rat (q : ℚ) : coefAB F n (algebraMap ℚ (Pmn F n) q) = q • (1 : AB F n) := by
  have h : (coefHom F n).comp (algebraMap ℚ (Pmn F n)) = algebraMap ℚ (AB F n) :=
    RingHom.ext_rat _ _
  rw [← coefHom_apply, ← RingHom.comp_apply, h, Algebra.algebraMap_eq_smul_one]

/-- The subalgebra spanned by the realization's generators and coefficients. -/
noncomputable def SAB : Subalgebra ℚ (AB F n) :=
  Algebra.adjoin ℚ (Set.range (BuAB F n) ∪ Set.range (aAB F n) ∪ {kappaAB F n}
    ∪ Set.range (coefAB F n))

theorem coefAB_commute_SAB (c : Pmn F n) (x : SAB F n) : Commute (coefAB F n c) (x : AB F n) := by
  obtain ⟨x, hx⟩ := x
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with ((⟨u, rfl⟩ | ⟨i, rfl⟩) | rfl) | ⟨d, rfl⟩
    · exact coefAB_comm_BuAB F n c u
    · exact coefAB_comm_aAB F n c i
    · exact (kappaAB_comm_coefAB F n c).symm
    · exact coefAB_comm_coefAB F n c d
  | algebraMap q => exact Algebra.commute_algebraMap_right q _
  | add y z _ _ hy hz => exact hy.add_right hz
  | mul y z _ _ hy hz => exact hy.mul_right hz

theorem coefAB_mem_SAB (c : Pmn F n) : coefAB F n c ∈ SAB F n :=
  Algebra.subset_adjoin <| (Or.inr ⟨c, rfl⟩)

/-- `coefAB` into `SAB F n`. -/
noncomputable def coefSAB : Pmn F n →+* SAB F n :=
  (coefHom F n).codRestrict (SAB F n) (coefAB_mem_SAB F n)

/-- `SAB F n` as a `P`-algebra, `P` acting through `coefAB`. -/
noncomputable instance : Algebra (Pmn F n) (SAB F n) :=
  (coefSAB F n).toAlgebra' fun c x => Subtype.ext (coefAB_commute_SAB F n c x)

theorem coe_algebraMap_SAB (c : Pmn F n) :
    ((algebraMap (Pmn F n) (SAB F n) c : SAB F n) : AB F n) = coefAB F n c := rfl

/-- The realization's generators, in `SAB F n`. -/
noncomputable def realizeGen : Gen (Bmn.I n) F.K → SAB F n
  | Sum.inl u => ⟨BuAB F n u, Algebra.subset_adjoin <| (Or.inl (Or.inl (Or.inl ⟨u, rfl⟩)))⟩
  | Sum.inr (Sum.inl i) => ⟨aAB F n i, Algebra.subset_adjoin <| (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))⟩
  | Sum.inr (Sum.inr _) => ⟨kappaAB F n, Algebra.subset_adjoin <| (Or.inl (Or.inr rfl))⟩

theorem realizeGen_rel (x y : FreeAlgebra (Pmn F n) (Gen (Bmn.I n) F.K))
    (h : Rel (jP F n) (gP F n) 0 x y) :
    FreeAlgebra.lift (Pmn F n) (realizeGen F n) x
      = FreeAlgebra.lift (Pmn F n) (realizeGen F n) y := by
  cases h with
  | bb u v =>
    apply Subtype.ext
    simp only [map_mul, map_add, AlgHom.commutes, bF, FreeAlgebra.lift_ι_apply, realizeGen,
      Subalgebra.coe_mul, Subalgebra.coe_add, coe_algebraMap_SAB, jP, coefAB_rat]
    rw [← sub_eq_iff_eq_add', BuAB_comm]
  | aa i j =>
    apply Subtype.ext
    simp only [map_mul, map_add, AlgHom.commutes, aF, FreeAlgebra.lift_ι_apply, realizeGen,
      Subalgebra.coe_mul, Subalgebra.coe_add, coe_algebraMap_SAB, gP, coefAB_rat]
    exact aAB_mul_add_swap F n i j
  | ba u i =>
    apply Subtype.ext
    simp only [map_mul, aF, bF, kF, FreeAlgebra.lift_ι_apply, realizeGen, Subalgebra.coe_mul,
      Pi.zero_apply, zero_smul, add_zero]
    exact BuAB_comm_aAB F n u i
  | kk =>
    apply Subtype.ext
    simp only [map_mul, map_zero, kF, FreeAlgebra.lift_ι_apply, realizeGen, Subalgebra.coe_mul,
      Subalgebra.coe_zero]
    exact kappaAB_sq F n
  | kb u =>
    apply Subtype.ext
    simp only [map_mul, kF, bF, FreeAlgebra.lift_ι_apply, realizeGen, Subalgebra.coe_mul]
    rw [kappaAB_comm_BuAB, gsign_10, one_smul]
  | ka i =>
    apply Subtype.ext
    simp only [map_mul, map_add, map_zero, kF, aF, FreeAlgebra.lift_ι_apply, realizeGen,
      Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_zero]
    rw [kappaAB_comm_aAB, gsign_11, neg_one_smul, neg_add_cancel]

/-- The map from the presented `A_0` to `SAB F n`, by the universal property. -/
noncomputable def realize : AZero F n →ₐ[Pmn F n] SAB F n :=
  liftSrc (realizeGen F n) (realizeGen_rel F n)

/-- `ρ : A_0 → AB`. -/
noncomputable def rho : AZero F n →+* AB F n := (SAB F n).val.toRingHom.comp (realize F n).toRingHom

variable {F n}

theorem rho_b (u : Bmn.I n) : rho F n (b _ _ 0 u) = BuAB F n u := by
  simp only [rho, b, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, realize,
    liftSrc_mk, bF, FreeAlgebra.lift_ι_apply, realizeGen]
  rfl
theorem rho_a (i : F.K) : rho F n (a _ _ 0 i) = aAB F n i := by
  simp only [rho, a, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, realize,
    liftSrc_mk, aF, FreeAlgebra.lift_ι_apply, realizeGen]
  rfl
theorem rho_κ : rho F n (κ _ _ 0) = kappaAB F n := by
  simp only [rho, κ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, realize,
    liftSrc_mk, kF, FreeAlgebra.lift_ι_apply, realizeGen]
  rfl
theorem rho_smul (c : Pmn F n) (x : AZero F n) : rho F n (c • x) = coefAB F n c * rho F n x := by
  rw [Algebra.smul_def, map_mul]
  congr 1
  simp only [rho, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    AlgHom.commutes]
  rfl

theorem rho_q4 (x : AZero F n) : rho F n (q4 F n • x) = (1 / 4 : ℚ) • rho F n x := by
  rw [rho_smul, q4, coefAB_rat, smul_one_mul]
theorem rho_q2 (x : AZero F n) : rho F n (q2 F n • x) = (1 / 2 : ℚ) • rho F n x := by
  rw [rho_smul, q2, coefAB_rat, smul_one_mul]

theorem rho_Xp (X : OspBasis F n) : rho F n (Xp 0 X) = X0 F n X := by
  match X with
  | .inl ⟨(u, v), _⟩ =>
    simp only [Xp, Lp, rho_q4, map_add, map_mul, rho_b]; rfl
  | .inr (.inl ⟨(i, j), _⟩) =>
    simp only [Xp, Sp, rho_q2, map_sub, map_mul, rho_a]; rfl
  | .inr (.inr (u, i)) =>
    simp only [Xp, Fp, rho_q4, map_add, map_mul, rho_a, rho_b]; rfl

theorem rho_iotaP (x : OspMod F n) : rho F n (iotaP 0 x) = iota0 F n x := by
  simp only [iotaP, map_sum, rho_smul, rho_Xp]
  rfl

/-! ## Prop 3.3 for the presented `A_0` -/

theorem iotaP_injective : Function.Injective (iotaP (F := F) (n := n) 0) := by
  intro x y h
  apply iota0_injective F n
  rw [← rho_iotaP, ← rho_iotaP, h]

theorem κ_mul_iotaP_injective {x y : OspMod F n}
    (h : κ _ _ 0 * iotaP 0 x = κ _ _ 0 * iotaP 0 y) : x = y := by
  apply kappa_iota0_injective F n
  have h' := congrArg (rho F n) h
  simpa only [map_mul, rho_κ, rho_iotaP] using h'

/-- **Prop 3.3 (Independence)**: `ι_0 : 𝔤_R → A_0` is injective, for the presented `A_0`. -/
theorem iotaRP_injective : Function.Injective (iotaRP (F := F) (n := n) 0) := by
  intro x y h
  unfold iotaRP at h
  have hκ := congrArg (fun z => κ _ _ 0 * z) h
  simp only [mul_add, ← mul_assoc, κ_mul_κ, zero_mul, add_zero] at hκ
  have h0 : falsePart x = falsePart y := κ_mul_iotaP_injective hκ
  rw [h0, add_right_inj] at h
  have h1 : truePart x = truePart y := κ_mul_iotaP_injective h
  funext ⟨i, b⟩
  cases b
  · exact congrFun h0 i
  · exact congrFun h1 i

end Presented
end OspN
end OspOddDeformations
