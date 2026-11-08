import OspOddDeformations.OspN.Multi.VChiBracket
import OspOddDeformations.OspN.Multi.Sigma
import OspOddDeformations.OspN.Multi.GRing

/-!
# Helper lemmas (`Θ_*` and `V_χ` composed on basis symbols)
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

-- Toolchain (v4.34): `OspBasis` is a plain `def` whose sum structure the proofs use; as in
-- `ThetaStarBracket.lean`, restore the pre-v4.34 type-transparency behaviour of `isDefEq` here.
set_option backward.isDefEq.respectTransparency.types false
-- `OspBasis` is a plain `def`, as in `ThetaStarBracket.lean` and `VChiBracket.lean`

variable {F : FermionIndex} {n r : ℕ}

/-- The matrix product, spelled out (the body of `mmul`). -/
noncomputable def mmul' (M M' : I n → I n → GR F n r) (u z : I n) : GR F n r :=
  ∑ w : I n, gmul (M u w) (M' w z)

theorem ThetaStar_S_basis (M : I n → I n → GR F n r) (i j : F.K) :
    linM (ThetaStarBasis0 M) (gtens gone (Sof i j)) = gtens gone (Sof i j) := by
  rw [linM_gtens, sum_emb0_Sof _ (ThetaStar_SCompat M), gsmul_gone_gtens]

theorem TSB0_comp (M M' : I n → I n → GR F n r) (hM : ∀ u w, IsEvenGR (M u w))
    (hM' : ∀ u w, IsEvenGR (M' u w)) (Z : OspBasis F n) :
    linM (ThetaStarBasis0 M') (ThetaStarBasis0 M Z) = ThetaStarBasis0 (mmul' M M') Z := by
  rcases Z with ⟨⟨u, v⟩, h⟩ | ⟨⟨i, j⟩, h⟩ | ⟨u, i⟩
  · change linM (ThetaStarBasis0 M')
        (∑ w : I n, ∑ z : I n, gtens (gmul (M u w) (M v z)) (eN (Lof w z))) =
      ∑ a : I n, ∑ b : I n, gtens (gmul (mmul' M M' u a) (mmul' M M' v b)) (eN (Lof a b))
    simp only [linM_sum, linM_gtens_eN, T0_Lof M' hM', gsmul_sum_right, gsmul_gtens, mmul',
      gmul_sum_left, gmul_sum_right, gtens_sum_left]
    have hc : ∀ w z a b : I n, gmul (gmul (M u w) (M v z)) (gmul (M' w a) (M' z b)) =
        gmul (gmul (M u w) (M' w a)) (gmul (M v z) (M' z b)) := by
      intro w z a b
      simp only [gmul_assoc]
      rw [← gmul_assoc (M v z), gmul_comm_of_even (hM v z) (M' w a), gmul_assoc]
    simp only [hc]
    calc _ = ∑ z : I n, ∑ w : I n, ∑ a : I n, ∑ b : I n,
            gtens (gmul (gmul (M u w) (M' w a)) (gmul (M v z) (M' z b))) (eN (Lof a b)) :=
          Finset.sum_comm
      _ = ∑ z : I n, ∑ a : I n, ∑ w : I n, ∑ b : I n,
            gtens (gmul (gmul (M u w) (M' w a)) (gmul (M v z) (M' z b))) (eN (Lof a b)) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ a : I n, ∑ z : I n, ∑ w : I n, ∑ b : I n,
            gtens (gmul (gmul (M u w) (M' w a)) (gmul (M v z) (M' z b))) (eN (Lof a b)) :=
          Finset.sum_comm
      _ = ∑ a : I n, ∑ z : I n, ∑ b : I n, ∑ w : I n,
            gtens (gmul (gmul (M u w) (M' w a)) (gmul (M v z) (M' z b))) (eN (Lof a b)) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  · have e1 : ThetaStarBasis0 M (Sum.inr (Sum.inl ⟨(i, j), h⟩) : OspBasis F n) =
        gtens gone (Sof i j) := rfl
    have e2 : ThetaStarBasis0 (mmul' M M') (Sum.inr (Sum.inl ⟨(i, j), h⟩) : OspBasis F n) =
        gtens gone (Sof i j) := rfl
    rw [e1, e2]
    exact ThetaStar_S_basis M' i j
  · change linM (ThetaStarBasis0 M') (∑ w : I n, gtens (M u w) (eN (Fof w i))) =
      ∑ z : I n, gtens (mmul' M M' u z) (eN (Fof z i))
    simp only [linM_sum, linM_gtens_eN, T0_F, gsmul_sum_right, gsmul_gtens, mmul', gtens_sum_left]
    exact Finset.sum_comm

/-! ## `V_χ` -/

theorem gmul_anticomm_odd {a b : GR F n r} (ha : HasParity 1 a) (hb : HasParity 1 b) :
    gmul a b = - gmul b a := by
  have h := gmul_comm_hom ha b
  have h1 : sigPow 1 b = - b := by
    have : (1 : ZMod 2) ≠ 0 := by decide
    simp [sigPow, this, GRing.sig_of_odd hb]
  rw [h1, gmul_neg_left] at h
  exact h

theorem VChi_S_basis (χ : I n → F.K → GR F n r) (i j : F.K) :
    linM (VBasis0 χ) (gtens gone (Sof i j)) = gtens gone (Sof i j) := by
  rw [linM_gtens, sum_emb0_Sof _ (fun _ _ _ => rfl), gsmul_gone_gtens]

theorem VChi_S_gen (χ : I n → F.K → GR F n r) (a : GR F n r) (i j : F.K) :
    linM (VBasis0 χ) (gtens a (Sof i j)) = gtens a (Sof i j) := by
  rw [linM_gtens, sum_emb0_Sof _ (fun _ _ _ => rfl), gsmul_gtens, gmul_gone]

theorem VB0_F (χ : I n → F.K → GR F n r) (u : I n) (i : F.K) :
    VBasis0 χ (Fof u i) =
      gtens gone (eN (Fof u i)) + (1 / 2 : ℚ) • ∑ j : F.K, gtens (χ u (F.dual j)) (Sof j i) := rfl

theorem VB0_L (χ : I n → F.K → GR F n r) (u v : I n) (h : Bmn.IKey u ≤ Bmn.IKey v) :
    VBasis0 χ (Sum.inl ⟨(u, v), h⟩) =
      gtens gone (eN (Lof u v)) + ∑ i : F.K, (gtens (χ v (F.dual i)) (eN (Fof u i)) +
        gtens (χ u (F.dual i)) (eN (Fof v i))) -
      (1 / 2 : ℚ) • ∑ i : F.K, ∑ j : F.K,
        gtens (gmul (χ u (F.dual i)) (χ v (F.dual j))) (Sof i j) := rfl

theorem VB0_comp_F (χ ψ : I n → F.K → GR F n r) (u : I n) (i : F.K) :
    linM (VBasis0 χ) (VBasis0 ψ (Fof u i)) = VBasis0 (χ + ψ) (Fof u i) := by
  rw [VB0_F ψ, VB0_F (χ + ψ)]
  simp only [linM_add, linM_rsmul, linM_sum, linM_gtens_eN, gsmul_gone, VB0_F, VChi_S_gen,
    Pi.add_apply, gtens_add_left]
  simp only [Finset.sum_add_distrib, smul_add]
  abel

theorem VB0_comp_L (χ ψ : I n → F.K → GR F n r) (hχ : ∀ u i, HasParity 1 (χ u i))
    (hψ : ∀ u i, HasParity 1 (ψ u i)) (u v : I n) (h : Bmn.IKey u ≤ Bmn.IKey v) :
    linM (VBasis0 χ) (VBasis0 ψ (Sum.inl ⟨(u, v), h⟩)) = VBasis0 (χ + ψ) (Sum.inl ⟨(u, v), h⟩) := by
  have hL : (Lof u v : OspBasis F n) = Sum.inl ⟨(u, v), h⟩ := Lof_of_le h
  rw [VB0_L ψ, VB0_L (χ + ψ)]
  simp only [linM_add, linM_sub, linM_rsmul, linM_sum, linM_gtens_eN, gsmul_gone, VB0_F,
    VChi_S_gen, gsmul_add_right, gsmul_rsmul_right, gsmul_sum_right, gsmul_gtens, gmul_gone,
    Pi.add_apply, gtens_add_left]
  have e0 : VBasis0 χ (Lof u v) = gtens gone (eN (Lof u v)) + ∑ i : F.K,
      (gtens (χ v (F.dual i)) (eN (Fof u i)) + gtens (χ u (F.dual i)) (eN (Fof v i))) -
      (1 / 2 : ℚ) • ∑ i : F.K, ∑ j : F.K,
        gtens (gmul (χ u (F.dual i)) (χ v (F.dual j))) (Sof i j) := by
    have := VB0_L χ u v h
    rw [← hL] at this
    exact this
  have hA : ∑ x : F.K, ∑ y : F.K, gtens (gmul (ψ v (F.dual x)) (χ u (F.dual y))) (Sof y x) =
      -∑ i : F.K, ∑ j : F.K, gtens (gmul (χ u (F.dual i)) (ψ v (F.dual j))) (Sof i j) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [gmul_anticomm_odd (hψ v (F.dual j)) (hχ u (F.dual i)), gtens_neg_left]
  have hB : ∑ x : F.K, ∑ y : F.K, gtens (gmul (ψ u (F.dual x)) (χ v (F.dual y))) (Sof y x) =
      -∑ i : F.K, ∑ j : F.K, gtens (gmul (ψ u (F.dual i)) (χ v (F.dual j))) (Sof i j) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Sof_antisymm j i, gtens_neg_right]
  rw [e0]
  simp only [gmul_add_left, gmul_add_right, gtens_add_left, Finset.sum_add_distrib, smul_add,
    ← Finset.smul_sum, hA, hB]
  module

theorem VB0_comp (χ ψ : I n → F.K → GR F n r) (hχ : ∀ u i, HasParity 1 (χ u i))
    (hψ : ∀ u i, HasParity 1 (ψ u i)) (Z : OspBasis F n) :
    linM (VBasis0 χ) (VBasis0 ψ Z) = VBasis0 (χ + ψ) Z := by
  rcases Z with ⟨⟨u, v⟩, h⟩ | ⟨⟨i, j⟩, h⟩ | ⟨u, i⟩
  · exact VB0_comp_L χ ψ hχ hψ u v h
  · exact VChi_S_basis χ i j
  · exact VB0_comp_F χ ψ u i

theorem linM_gone_eN (x : RModM F n r) : linM (fun Z => gtens gone (eN Z)) x = x := by
  refine RModM_ext_grComp fun W => ?_
  rw [grComp_linM]
  simp only [grComp_gtens, gmul_smul_right, gmul_gone, emb0_eN]
  simp

theorem gtens_zero_left' (v : OspMod F n) : gtens (0 : GR F n r) v = 0 := by
  funext p; simp [gtens_apply]

theorem VB0_zero (Z : OspBasis F n) :
    VBasis0 (0 : I n → F.K → GR F n r) Z = gtens gone (eN Z) := by
  rcases Z with ⟨⟨u, v⟩, h⟩ | ⟨⟨i, j⟩, h⟩ | ⟨u, i⟩
  · rw [VB0_L, Lof_of_le h]
    simp [gtens_zero_left', gmul_zero_left]
  · change gtens gone (Sof i j) = _
    rw [Sof_of_lt h]
  · change VBasis0 0 (Fof u i) = gtens gone (eN (Fof u i))
    rw [VB0_F]
    simp [gtens_zero_left']

theorem VChi_zero (x : RModM F n r) : VChi (0 : I n → F.K → GR F n r) x = x := by
  rw [VChi_eq_linM]
  have : VBasis0 (0 : I n → F.K → GR F n r) = fun Z => gtens gone (eN Z) := funext VB0_zero
  rw [this]
  exact linM_gone_eN x

theorem VChi_comp' (χ ψ : I n → F.K → GR F n r) (hχ : ∀ u i, HasParity 1 (χ u i))
    (hψ : ∀ u i, HasParity 1 (ψ u i)) (x : RModM F n r) :
    VChi χ (VChi ψ x) = VChi (χ + ψ) x := by
  rw [VChi_eq_linM, VChi_eq_linM, VChi_eq_linM, linM_comp]
  congr 1
  funext Z
  exact VB0_comp χ ψ hχ hψ Z

theorem HasParity_gmono_singleton (s : Fin r) (c : PmnR F n r) : HasParity 1 (gmono {s} c) := by
  intro T hT
  unfold gmono
  refine ite_eq_right_iff.mpr fun h => ?_
  subst h
  exact absurd (by simp) hT

theorem HasParity_zero' (π : ZMod 2) : HasParity π (0 : GR F n r) := fun _ _ => rfl

theorem HasParity_add' {π : ZMod 2} {a b : GR F n r} (ha : HasParity π a) (hb : HasParity π b) :
    HasParity π (a + b) := fun T hT => by
  simp [ha T hT, hb T hT]

theorem odd_list_sum {ι : Type*} (f : ι → I n → F.K → GR F n r)
    (hf : ∀ s u i, HasParity 1 (f s u i))
    (l : List ι) (u : I n) (i : F.K) : HasParity 1 ((l.map fun s => f s u i).sum) := by
  induction l with
  | nil => exact HasParity_zero' 1
  | cons s l ih => rw [List.map_cons, List.sum_cons]; exact HasParity_add' (hf s u i) ih

theorem foldr_VChi (f : Fin r → I n → F.K → GR F n r) (hf : ∀ s u i, HasParity 1 (f s u i))
    (l : List (Fin r)) (y : RModM F n r) :
    (l.foldr (fun s g => VChi (f s) ∘ g) id) y =
      VChi (fun u i => (l.map fun s => f s u i).sum) y := by
  induction l generalizing y with
  | nil => exact (VChi_zero y).symm
  | cons s l ih =>
    simp only [List.foldr_cons, Function.comp_apply]
    rw [ih]
    rw [VChi_comp' _ _ (hf s) (fun u i => odd_list_sum f hf l u i)]
    congr 1

end Multi
end OspN
end OspOddDeformations
