import OspOddDeformations.OspN.Multi.BracketCalc
import OspOddDeformations.OspN.Multi.Theta
import OspOddDeformations.OspN.Multi.GRing

/-!
# `Θ_*` intertwines `[·,·]_{J-Ω}` with `[·,·]_0` (statement (i) of `Multi/FactorDefs.lean`)
-/

-- Toolchain (v4.34): `OspBasis` is a plain `def` whose sum structure the proofs use; as in
-- `Coboundary.lean` etc., restore the pre-v4.34 type-transparency behaviour of `isDefEq` here.
set_option backward.isDefEq.respectTransparency.types false

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

theorem ThetaStar_parity (Θ : I n → I n → GR F n r) (hEven : ∀ u w, IsEvenGR (Θ u w))
    (X W : OspBasis F n) : HasParity (parity X + parity W) (grComp (ThetaStarBasis0 Θ X) W) := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases X with ⟨⟨u, v⟩, h⟩ | ⟨⟨i, j⟩, h⟩ | ⟨u, i⟩
  · have h0 : parity (Sum.inl ⟨(u, v), h⟩ : OspBasis F n) = 0 := rfl
    rw [h0, zero_add]
    simp only [ThetaStarBasis0, grComp_sum, grComp_gtens]
    refine HasParity.sum _ fun w _ => HasParity.sum _ fun z _ => ?_
    refine HasParity.smul_of ((hEven u w).parity.gmul (hEven v z).parity) _ fun hc => ?_
    rw [parity_of_emb0_eN hc, parity_Lof]; simp
  · have h0 : parity (Sum.inr (Sum.inl ⟨(i, j), h⟩) : OspBasis F n) = 0 := rfl
    rw [h0, zero_add]
    simp only [ThetaStarBasis0, grComp_gtens]
    refine HasParity.smul_of (HasCard_gone (F := F) (n := n) (r := r)).parity _ fun hc => ?_
    rw [parity_of_emb0_Sof hc]; simp
  · have h0 : parity (Sum.inr (Sum.inr (u, i)) : OspBasis F n) = 1 := rfl
    rw [h0]
    simp only [ThetaStarBasis0, grComp_sum, grComp_gtens]
    refine HasParity.sum _ fun w _ => ?_
    refine HasParity.smul_of (hEven u w).parity _ fun hc => ?_
    rw [parity_of_emb0_eN hc, parity_Fof]; simp [h11]

theorem bracketLL_swap_left (u v w z : I n) :
    bracketLL (F := F) u v w z = bracketLL v u w z := by
  unfold bracketLL; abel

theorem bracketLL_swap_right (u v w z : I n) :
    bracketLL (F := F) u v w z = bracketLL u v z w := by
  unfold bracketLL; abel

theorem bracket0Basis_Lof_Lof (w z a b : I n) :
    bracket0Basis (Lof w z : OspBasis F n) (Lof a b) = bracketLL w z a b := by
  have hL : ∀ x y : I n, ∃ p : I n × I n, ∃ h : Bmn.IKey p.1 ≤ Bmn.IKey p.2,
      (Lof x y : OspBasis F n) = Sum.inl ⟨p, h⟩ ∧ (p = (x, y) ∨ p = (y, x)) := by
    intro x y
    by_cases h : Bmn.IKey x ≤ Bmn.IKey y
    · exact ⟨(x, y), h, Lof_of_le h, Or.inl rfl⟩
    · refine ⟨(y, x), (Nat.not_le.mp h).le, ?_, Or.inr rfl⟩
      unfold Lof; exact dite_eq_right h
  obtain ⟨⟨p1, p2⟩, h1, e1, hp⟩ := hL w z
  obtain ⟨⟨q1, q2⟩, h2, e2, hq⟩ := hL a b
  rw [e1, e2]
  change bracketLL p1 p2 q1 q2 = _
  rcases hp with hp | hp <;> rcases hq with hq | hq <;>
    simp only [Prod.mk.injEq] at hp hq <;> obtain ⟨rfl, rfl⟩ := hp <;> obtain ⟨rfl, rfl⟩ := hq
  · rfl
  · exact bracketLL_swap_right _ _ _ _ |>.symm
  · exact bracketLL_swap_left _ _ _ _ |>.symm
  · rw [bracketLL_swap_left, bracketLL_swap_right, bracketLL_swap_left, bracketLL_swap_right]

theorem T0_Lof (Θ : I n → I n → GR F n r) (hEven : ∀ u w, IsEvenGR (Θ u w)) (u t : I n) :
    ThetaStarBasis0 Θ (Lof u t) =
      ∑ w : I n, ∑ b : I n, gtens (gmul (Θ u w) (Θ t b)) (eN (Lof w b)) := by
  by_cases h : Bmn.IKey u ≤ Bmn.IKey t
  · rw [Lof_of_le h]; rfl
  · have e : (Lof u t : OspBasis F n) = Sum.inl ⟨(t, u), (Nat.not_le.mp h).le⟩ := by
      unfold Lof; exact dite_eq_right h
    rw [e]
    change ∑ w : I n, ∑ b : I n, gtens (gmul (Θ t w) (Θ u b)) (eN (Lof w b)) = _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun b _ => ?_
    rw [gmul_comm_of_even (hEven u w), Lof_comm w b]

theorem IsEvenGR_JmOmega (u v : I n) : IsEvenGR (JmOmega (F := F) (r := r) u v) := by
  intro T hT
  have h1 := (HasCard_JR (F := F) (r := r) u v).isEven (by norm_num) T hT
  have h2 := (HasCard_OmegaR (F := F) (r := r) u v).isEven (by norm_num) T hT
  simp [JmOmega, h1, h2]

theorem contract_basic (Θ : I n → I n → GR F n r)
    (hΘ : ∀ u v, thetaJthetaT Θ u v = JR u v - OmegaR u v) (v s : I n) :
    ∑ z : I n, ∑ a : I n, (MvPolynomial.C (J n z a) : PmnR F n r) • gmul (Θ v z) (Θ s a)
      = JmOmega v s := by
  have h := hΘ v s
  unfold thetaJthetaT at h
  simp only [gmul_JR_left, gmul_smul_right] at h
  exact h

theorem contract_gen (c : I n → I n → PmnR F n r) (L R : GR F n r) (f g : I n → GR F n r) :
    ∑ z : I n, ∑ a : I n, c z a • gmul (gmul L (f z)) (gmul (g a) R)
      = gmul L (gmul (∑ z : I n, ∑ a : I n, c z a • gmul (f z) (g a)) R) := by
  simp only [gmul_sum_left, gmul_sum_right, gmul_smul_left, gmul_smul_right, gmul_assoc]

theorem hv_eN (b : OspBasis F n) :
    ∀ W, emb0 (F := F) (n := n) (r := r) (eN b W) ≠ 0 → W = b := fun _ h => parity_of_emb0_eN h

theorem liftB0_gtens_eN (a a' : GR F n r) (b b' : OspBasis F n) :
    liftB B0data (gtens a (eN b)) (gtens a' (eN b')) =
      gtens (gmul a (sigPow (parity b) a')) (bracket0Basis b b') := by
  rw [liftB0_gtens a a' (eN b) (eN b') (parity b) (fun W h => by rw [hv_eN b W h]),
    bracket0_eN_eN]

theorem rsmul_eq_C_smul (q : ℚ) (a : GR F n r) :
    q • a = (MvPolynomial.C q : PmnR F n r) • a := by
  funext T; simp [MvPolynomial.smul_eq_C_mul]

theorem contract_basic_rat (Θ : I n → I n → GR F n r)
    (hΘ : ∀ u v, thetaJthetaT Θ u v = JR u v - OmegaR u v) (v s : I n) :
    ∑ z : I n, ∑ a : I n, (J n z a) • gmul (Θ v z) (Θ s a) = JmOmega (F := F) (r := r) v s := by
  rw [← contract_basic Θ hΘ v s]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun a _ => ?_
  exact rsmul_eq_C_smul _ _

theorem contract_gen_rat (c : I n → I n → ℚ) (L R : GR F n r) (f g : I n → GR F n r) :
    ∑ z : I n, ∑ a : I n, c z a • gmul (gmul L (f z)) (gmul (g a) R)
      = gmul L (gmul (∑ z : I n, ∑ a : I n, c z a • gmul (f z) (g a)) R) := by
  simp only [gmul_sum_left, gmul_sum_right, gmul_rsmul_left, gmul_rsmul_right, gmul_assoc]

theorem sum_perm4 {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid M] (f : α → β → γ → δ → M) :
    ∑ a, ∑ b, ∑ w, ∑ z, f a b w z = ∑ w, ∑ b, ∑ z, ∑ a, f a b w z := by
  calc ∑ a, ∑ b, ∑ w, ∑ z, f a b w z = ∑ b, ∑ a, ∑ w, ∑ z, f a b w z := Finset.sum_comm
    _ = ∑ b, ∑ w, ∑ a, ∑ z, f a b w z :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ w, ∑ b, ∑ a, ∑ z, f a b w z := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm

theorem gmul_left_comm_of_even {a : GR F n r} (ha : IsEvenGR a) (x y : GR F n r) :
    gmul x (gmul a y) = gmul a (gmul x y) := by
  rw [← gmul_assoc, ← gmul_comm_of_even ha x, gmul_assoc]

theorem shape1 (Θ : I n → I n → GR F n r)
    (hΘ : ∀ u v, thetaJthetaT Θ u v = JR u v - OmegaR u v) (u v s t : I n) :
    ∑ a : I n, ∑ b : I n, ∑ w : I n, ∑ z : I n, (1 / 2 * J n z a) •
        gtens (gmul (gmul (Θ u w) (Θ v z)) (gmul (Θ s a) (Θ t b))) (eN (Lof w b))
      = (1 / 2 : ℚ) • gsmul (JmOmega v s)
          (∑ w : I n, ∑ b : I n, gtens (gmul (Θ u w) (Θ t b)) (eN (Lof w b))) := by
  rw [sum_perm4, gsmul_sum_right, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [gsmul_sum_right, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [gsmul_gtens, gtens_rsmul_left]
  simp only [gtens_rsmul_left, ← gtens_sum_left]
  congr 1
  rw [contract_gen_rat (fun z a => 1 / 2 * J n z a) (Θ u w) (Θ t b) (Θ v) (Θ s)]
  have h : ∑ z : I n, ∑ a : I n, (1 / 2 * J n z a) • gmul (Θ v z) (Θ s a) =
      (1 / 2 : ℚ) • JmOmega (F := F) (r := r) v s := by
    rw [← contract_basic_rat Θ hΘ v s, Finset.smul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => mul_smul _ _ _
  rw [h, gmul_rsmul_left, gmul_rsmul_right]
  exact congrArg (fun q => (1 / 2 : ℚ) • q) (gmul_left_comm_of_even (IsEvenGR_JmOmega v s) _ _)

theorem shape2 (Θ : I n → I n → GR F n r) (hEven : ∀ u w, IsEvenGR (Θ u w))
    (hΘ : ∀ u v, thetaJthetaT Θ u v = JR u v - OmegaR u v) (u v s t : I n) :
    ∑ a : I n, ∑ b : I n, ∑ w : I n, ∑ z : I n, (1 / 2 * J n w a) •
        gtens (gmul (gmul (Θ u w) (Θ v z)) (gmul (Θ s a) (Θ t b))) (eN (Lof z b))
      = (1 / 2 : ℚ) • gsmul (JmOmega u s)
          (∑ w : I n, ∑ b : I n, gtens (gmul (Θ v w) (Θ t b)) (eN (Lof w b))) := by
  rw [← shape1 Θ hΘ v u s t]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun z _ => ?_
  rw [gmul_comm_of_even (hEven u z) (Θ v w)]

theorem shape3 (Θ : I n → I n → GR F n r) (hEven : ∀ u w, IsEvenGR (Θ u w))
    (hΘ : ∀ u v, thetaJthetaT Θ u v = JR u v - OmegaR u v) (u v s t : I n) :
    ∑ a : I n, ∑ b : I n, ∑ w : I n, ∑ z : I n, (1 / 2 * J n z b) •
        gtens (gmul (gmul (Θ u w) (Θ v z)) (gmul (Θ s a) (Θ t b))) (eN (Lof w a))
      = (1 / 2 : ℚ) • gsmul (JmOmega v t)
          (∑ w : I n, ∑ b : I n, gtens (gmul (Θ u w) (Θ s b)) (eN (Lof w b))) := by
  rw [← shape1 Θ hΘ u v t s, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun z _ => ?_
  rw [gmul_comm_of_even (hEven s a) (Θ t b)]

theorem shape4 (Θ : I n → I n → GR F n r) (hEven : ∀ u w, IsEvenGR (Θ u w))
    (hΘ : ∀ u v, thetaJthetaT Θ u v = JR u v - OmegaR u v) (u v s t : I n) :
    ∑ a : I n, ∑ b : I n, ∑ w : I n, ∑ z : I n, (1 / 2 * J n w b) •
        gtens (gmul (gmul (Θ u w) (Θ v z)) (gmul (Θ s a) (Θ t b))) (eN (Lof z a))
      = (1 / 2 : ℚ) • gsmul (JmOmega u t)
          (∑ w : I n, ∑ b : I n, gtens (gmul (Θ v w) (Θ s b)) (eN (Lof w b))) := by
  rw [← shape1 Θ hΘ v u t s]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
  rw [gmul_comm_of_even (hEven u w) (Θ v z), gmul_comm_of_even (hEven s a) (Θ t b)]

theorem VecLL (Θ : I n → I n → GR F n r) (hEven : ∀ u w, IsEvenGR (Θ u w))
    (hΘ : ∀ u v, thetaJthetaT Θ u v = JR u v - OmegaR u v) (u v s t : I n)
    (h1 : Bmn.IKey u ≤ Bmn.IKey v) (h2 : Bmn.IKey s ≤ Bmn.IKey t) :
    liftB B0data (ThetaStarBasis0 Θ (Sum.inl ⟨(u, v), h1⟩))
        (ThetaStarBasis0 Θ (Sum.inl ⟨(s, t), h2⟩)) =
      linM (ThetaStarBasis0 Θ)
        (bracketJBasis0 JmOmega (Sum.inl ⟨(u, v), h1⟩) (Sum.inl ⟨(s, t), h2⟩)) := by
  change liftB B0data (∑ w : I n, ∑ z : I n, gtens (gmul (Θ u w) (Θ v z)) (eN (Lof w z)))
      (∑ a : I n, ∑ b : I n, gtens (gmul (Θ s a) (Θ t b)) (eN (Lof a b))) = _
  simp only [liftB_sum_left, liftB_sum_right, liftB0_gtens_eN, parity_Lof, sigPow_zero,
    bracket0Basis_Lof_Lof, bracketLL, gtens_add_right, gtens_rsmul_right, Finset.sum_add_distrib]
  simp only [bracketJBasis0, linM_rsmul, linM_add, linM_gtens_eN, T0_Lof Θ hEven]
  rw [shape1 Θ hΘ, shape2 Θ hEven hΘ, shape3 Θ hEven hΘ, shape4 Θ hEven hΘ]
  simp only [smul_add]

theorem Lof_cases (x y : I n) : ∃ p : I n × I n, ∃ h : Bmn.IKey p.1 ≤ Bmn.IKey p.2,
    (Lof x y : OspBasis F n) = Sum.inl ⟨p, h⟩ := by
  by_cases h : Bmn.IKey x ≤ Bmn.IKey y
  · exact ⟨(x, y), h, Lof_of_le h⟩
  · refine ⟨(y, x), (Nat.not_le.mp h).le, ?_⟩
    unfold Lof; exact dite_eq_right h

theorem bracket0_Lof_Sof (w z : I n) (k l : F.K) :
    bracket0 (eN (Lof w z : OspBasis F n)) (Sof k l) = 0 := by
  obtain ⟨⟨p1, p2⟩, h, e⟩ := Lof_cases (F := F) w z
  rw [e]
  exact bracket0_L_Sof p1 p2 h k l

theorem bracket0_Sof_Lof (k l : F.K) (w z : I n) :
    bracket0 (Sof k l) (eN (Lof w z : OspBasis F n)) = 0 := by
  obtain ⟨⟨p1, p2⟩, h, e⟩ := Lof_cases (F := F) w z
  rw [e]
  rcases lt_trichotomy (F.key k) (F.key l) with hk | hk | hk
  · rw [Sof_of_lt hk, bracket0_eN_eN]; rfl
  · have : (Sof k l : OspMod F n) = 0 := by
      unfold Sof
      have h1 : ¬ F.key k < F.key l := by omega
      have h2 : ¬ F.key l < F.key k := by omega
      simp only [h1, h2, ↓reduceDIte]
    rw [this, bracket0_zero_left]
  · rw [Sof_antisymm k l, bracket0_neg_left, Sof_of_lt hk, bracket0_eN_eN]
    simp [bracket0Basis]

theorem hv_Sof (i j : F.K) :
    ∀ W, emb0 (F := F) (n := n) (r := r) (Sof i j W) ≠ 0 → parity W = 0 :=
  fun _ h => parity_of_emb0_Sof h

theorem hv_Lof (w z : I n) :
    ∀ W, emb0 (F := F) (n := n) (r := r) (eN (Lof w z : OspBasis F n) W) ≠ 0 → parity W = 0 :=
  fun W h => by rw [parity_of_emb0_eN h, parity_Lof]

theorem VecLS (Θ : I n → I n → GR F n r) (u v : I n)
    (h1 : Bmn.IKey u ≤ Bmn.IKey v) (k l : F.K) (h2 : F.key k < F.key l) :
    liftB B0data (ThetaStarBasis0 Θ (Sum.inl ⟨(u, v), h1⟩))
        (ThetaStarBasis0 Θ (Sum.inr (Sum.inl ⟨(k, l), h2⟩))) =
      linM (ThetaStarBasis0 Θ)
        (bracketJBasis0 JmOmega (Sum.inl ⟨(u, v), h1⟩) (Sum.inr (Sum.inl ⟨(k, l), h2⟩))) := by
  change liftB B0data (∑ w : I n, ∑ z : I n, gtens (gmul (Θ u w) (Θ v z)) (eN (Lof w z)))
      (gtens gone (Sof k l)) = linM (ThetaStarBasis0 Θ) 0
  rw [linM_zero, liftB_sum_left]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [liftB_sum_left]
  refine Finset.sum_eq_zero fun z _ => ?_
  rw [liftB0_gtens _ _ _ _ 0 (hv_Lof w z), bracket0_Lof_Sof, gtens_zero_right]

theorem VecSL (Θ : I n → I n → GR F n r) (u v : I n)
    (h1 : Bmn.IKey u ≤ Bmn.IKey v) (k l : F.K) (h2 : F.key k < F.key l) :
    liftB B0data (ThetaStarBasis0 Θ (Sum.inr (Sum.inl ⟨(k, l), h2⟩)))
        (ThetaStarBasis0 Θ (Sum.inl ⟨(u, v), h1⟩)) =
      linM (ThetaStarBasis0 Θ)
        (bracketJBasis0 JmOmega (Sum.inr (Sum.inl ⟨(k, l), h2⟩)) (Sum.inl ⟨(u, v), h1⟩)) := by
  change liftB B0data (gtens gone (Sof k l))
      (∑ w : I n, ∑ z : I n, gtens (gmul (Θ u w) (Θ v z)) (eN (Lof w z))) =
      linM (ThetaStarBasis0 Θ) 0
  rw [linM_zero, liftB_sum_right]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [liftB_sum_right]
  refine Finset.sum_eq_zero fun z _ => ?_
  rw [liftB0_gtens _ _ _ _ 0 (hv_Sof k l), bracket0_Sof_Lof, gtens_zero_right]

/-- The linear extension of `A0` to `OspMod`-vectors (the `V`-coefficients, `κ`-degree `0`). -/
noncomputable def extT (A0 : OspBasis F n → RModM F n r) (v : OspMod F n) : RModM F n r :=
  ∑ Y : OspBasis F n, emb0 (r := r) (v Y) • A0 Y

theorem linM_gtens' (A0 : OspBasis F n → RModM F n r) (a : GR F n r) (v : OspMod F n) :
    linM A0 (gtens a v) = gsmul a (extT A0 v) := linM_gtens A0 a v

theorem extT_add (A0 : OspBasis F n → RModM F n r) (v w : OspMod F n) :
    extT A0 (v + w) = extT A0 v + extT A0 w := by
  unfold extT; simp only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]

theorem extT_neg (A0 : OspBasis F n → RModM F n r) (v : OspMod F n) :
    extT A0 (-v) = - extT A0 v := by
  unfold extT; simp only [Pi.neg_apply, map_neg, neg_smul, Finset.sum_neg_distrib]

theorem extT_sub (A0 : OspBasis F n → RModM F n r) (v w : OspMod F n) :
    extT A0 (v - w) = extT A0 v - extT A0 w := by
  rw [sub_eq_add_neg, extT_add, extT_neg, ← sub_eq_add_neg]

theorem extT_rsmul (A0 : OspBasis F n → RModM F n r) (q : ℚ) (v : OspMod F n) :
    extT A0 (q • v) = q • extT A0 v := by
  unfold extT
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  simp only [Pi.smul_apply, map_smul, smul_assoc]

theorem extT_eN (A0 : OspBasis F n → RModM F n r) (b : OspBasis F n) :
    extT A0 (eN b) = A0 b := sum_emb0_eN A0 b

theorem extT_Sof (A0 : OspBasis F n → RModM F n r) (hS : SCompat A0) (i j : F.K) :
    extT A0 (Sof i j) = gtens gone (Sof i j) := sum_emb0_Sof A0 hS i j

theorem gtens_sub_right (a : GR F n r) (v w : OspMod F n) :
    gtens a (v - w) = gtens a v - gtens a w := by
  funext p; simp [gtens_apply, mul_sub]

theorem extT_bracketSS (Θ : I n → I n → GR F n r) (i j k l : F.K) :
    extT (ThetaStarBasis0 Θ) (bracketSS i j k l : OspMod F n) =
      gtens gone (bracketSS i j k l : OspMod F n) := by
  unfold bracketSS
  simp only [extT_add, extT_sub, extT_rsmul, extT_Sof _ (ThetaStar_SCompat Θ), gtens_add_right,
    gtens_sub_right, gtens_rsmul_right]

theorem VecSS (Θ : I n → I n → GR F n r) (i j k l : F.K) (h1 : F.key i < F.key j)
    (h2 : F.key k < F.key l) :
    liftB B0data (ThetaStarBasis0 Θ (Sum.inr (Sum.inl ⟨(i, j), h1⟩)))
        (ThetaStarBasis0 Θ (Sum.inr (Sum.inl ⟨(k, l), h2⟩))) =
      linM (ThetaStarBasis0 Θ)
        (bracketJBasis0 JmOmega (Sum.inr (Sum.inl ⟨(i, j), h1⟩))
          (Sum.inr (Sum.inl ⟨(k, l), h2⟩))) := by
  change liftB B0data (gtens gone (Sof i j)) (gtens gone (Sof k l)) =
    linM (ThetaStarBasis0 Θ) (gtens gone (bracketSS i j k l))
  rw [liftB0_gtens _ _ _ _ 0 (hv_Sof i j), linM_gtens', extT_bracketSS, gsmul_gone_gtens,
    sigPow_zero, gmul_gone, Sof_of_lt h1, bracket0_S_Sof i j h1 k l]

theorem bracketLF_swap (u v w : I n) (i : F.K) :
    bracketLF (F := F) u v w i = bracketLF v u w i := by
  unfold bracketLF; abel

theorem bracket0Basis_Lof_Fof (w z a : I n) (i : F.K) :
    bracket0Basis (Lof w z : OspBasis F n) (Fof a i) = bracketLF w z a i := by
  obtain ⟨⟨p1, p2⟩, h, e⟩ := Lof_cases (F := F) w z
  rw [e]
  have hp : (p1 = w ∧ p2 = z) ∨ (p1 = z ∧ p2 = w) := by
    by_cases hh : Bmn.IKey w ≤ Bmn.IKey z
    · have := Lof_of_le (F := F) hh
      rw [e] at this
      have h2 := Sum.inl.inj this
      have h3 := congrArg (fun x => x.1) h2
      simp only [Prod.mk.injEq] at h3
      exact Or.inl ⟨h3.1, h3.2⟩
    · have e2 : (Lof w z : OspBasis F n) = Sum.inl ⟨(z, w), (Nat.not_le.mp hh).le⟩ := by
        unfold Lof; exact dite_eq_right hh
      rw [e] at e2
      have h2 := Sum.inl.inj e2
      have h3 := congrArg (fun x => x.1) h2
      simp only [Prod.mk.injEq] at h3
      exact Or.inr ⟨h3.1, h3.2⟩
  change bracketLF p1 p2 a i = _
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact bracketLF_swap _ _ _ _

theorem bracket0Basis_Fof_Lof (a : I n) (i : F.K) (w z : I n) :
    bracket0Basis (Fof a i : OspBasis F n) (Lof w z) = - bracketLF w z a i := by
  obtain ⟨⟨p1, p2⟩, h, e⟩ := Lof_cases (F := F) w z
  have hp : (p1 = w ∧ p2 = z) ∨ (p1 = z ∧ p2 = w) := by
    by_cases hh : Bmn.IKey w ≤ Bmn.IKey z
    · have := Lof_of_le (F := F) hh
      rw [e] at this
      have h3 := congrArg (fun x => x.1) (Sum.inl.inj this)
      simp only [Prod.mk.injEq] at h3
      exact Or.inl ⟨h3.1, h3.2⟩
    · have e2 : (Lof w z : OspBasis F n) = Sum.inl ⟨(z, w), (Nat.not_le.mp hh).le⟩ := by
        unfold Lof; exact dite_eq_right hh
      rw [e] at e2
      have h3 := congrArg (fun x => x.1) (Sum.inl.inj e2)
      simp only [Prod.mk.injEq] at h3
      exact Or.inr ⟨h3.1, h3.2⟩
  rw [e]
  change - bracketLF p1 p2 a i = _
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · rw [bracketLF_swap]

theorem hv_Fof (w : I n) (i : F.K) :
    ∀ W, emb0 (F := F) (n := n) (r := r) (eN (Fof w i : OspBasis F n) W) ≠ 0 → parity W = 1 :=
  fun W h => by rw [parity_of_emb0_eN h, parity_Fof]

theorem sigPow_of_even (π : ZMod 2) {a : GR F n r} (ha : IsEvenGR a) : sigPow π a = a := by
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hz π with rfl | rfl
  · exact sigPow_zero a
  · have h1 : (1 : ZMod 2) ≠ 0 := by decide
    unfold sigPow
    rw [ite_eq_right h1]
    funext T
    by_cases hT : T.card % 2 = 1
    · have h0 := ha T hT
      simp [sig, h0]
    · have : T.card % 2 = 0 := by omega
      simp [sig, Nat.even_iff.mpr this |>.neg_one_pow]

theorem T0_F (Θ : I n → I n → GR F n r) (a : I n) (x : F.K) :
    ThetaStarBasis0 Θ (Fof a x) = ∑ w : I n, gtens (Θ a w) (eN (Fof w x)) := rfl

theorem contract_gen_rat3 (c : I n → I n → ℚ) (L : GR F n r) (f g : I n → GR F n r) :
    ∑ z : I n, ∑ a : I n, c z a • gmul (gmul L (f z)) (g a)
      = gmul L (∑ z : I n, ∑ a : I n, c z a • gmul (f z) (g a)) := by
  simp only [gmul_sum_right, gmul_rsmul_right, gmul_assoc]

theorem sum_perm3 {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M]
    (f : α → β → γ → M) : ∑ a, ∑ w, ∑ z, f a w z = ∑ w, ∑ z, ∑ a, f a w z := by
  calc ∑ a, ∑ w, ∑ z, f a w z = ∑ w, ∑ a, ∑ z, f a w z := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun w _ => Finset.sum_comm

theorem sum_gtens_rat (c : I n → I n → ℚ) (P : I n → I n → GR F n r) (e : OspMod F n) :
    ∑ z : I n, ∑ a : I n, c z a • gtens (P z a) e
      = gtens (∑ z : I n, ∑ a : I n, c z a • P z a) e := by
  simp only [gtens_rsmul_left, ← gtens_sum_left]

theorem shapeF1 (Θ : I n → I n → GR F n r)
    (hΘ : ∀ u v, thetaJthetaT Θ u v = JR u v - OmegaR u v) (u v s : I n) (i : F.K) :
    ∑ a : I n, ∑ w : I n, ∑ z : I n, (1 / 2 * J n z a) •
        gtens (gmul (gmul (Θ u w) (Θ v z)) (Θ s a)) (eN (Fof w i))
      = (1 / 2 : ℚ) • gsmul (JmOmega v s) (∑ w : I n, gtens (Θ u w) (eN (Fof w i))) := by
  rw [sum_perm3, gsmul_sum_right, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [gsmul_gtens, gtens_rsmul_left, sum_gtens_rat (fun z a => 1 / 2 * J n z a)
    (fun z a => gmul (gmul (Θ u w) (Θ v z)) (Θ s a))]
  refine congrArg (fun q => gtens q (eN (Fof w i))) ?_
  rw [contract_gen_rat3 (fun z a => 1 / 2 * J n z a) (Θ u w) (Θ v) (Θ s)]
  have h : ∑ z : I n, ∑ a : I n, (1 / 2 * J n z a) • gmul (Θ v z) (Θ s a) =
      (1 / 2 : ℚ) • JmOmega (F := F) (r := r) v s := by
    rw [← contract_basic_rat Θ hΘ v s, Finset.smul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => mul_smul _ _ _
  rw [h, gmul_rsmul_right, gmul_comm_of_even (IsEvenGR_JmOmega v s)]

theorem shapeF2 (Θ : I n → I n → GR F n r) (hEven : ∀ u w, IsEvenGR (Θ u w))
    (hΘ : ∀ u v, thetaJthetaT Θ u v = JR u v - OmegaR u v) (u v s : I n) (i : F.K) :
    ∑ a : I n, ∑ w : I n, ∑ z : I n, (1 / 2 * J n w a) •
        gtens (gmul (gmul (Θ u w) (Θ v z)) (Θ s a)) (eN (Fof z i))
      = (1 / 2 : ℚ) • gsmul (JmOmega u s) (∑ w : I n, gtens (Θ v w) (eN (Fof w i))) := by
  rw [← shapeF1 Θ hΘ v u s i]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun z _ => ?_
  rw [gmul_comm_of_even (hEven u z) (Θ v w)]

theorem bracketJBasis0_L_F (J' : I n → I n → GR F n r) (u v w : I n) (h : Bmn.IKey u ≤ Bmn.IKey v)
    (i : F.K) :
    bracketJBasis0 J' (Sum.inl ⟨(u, v), h⟩) (Fof w i) =
      (1 / 2 : ℚ) • (gtens (J' v w) (eN (Fof u i)) + gtens (J' u w) (eN (Fof v i))) := rfl

theorem VecLF (Θ : I n → I n → GR F n r) (hEven : ∀ u w, IsEvenGR (Θ u w))
    (hΘ : ∀ u v, thetaJthetaT Θ u v = JR u v - OmegaR u v) (u v s : I n)
    (h1 : Bmn.IKey u ≤ Bmn.IKey v) (i : F.K) :
    liftB B0data (ThetaStarBasis0 Θ (Sum.inl ⟨(u, v), h1⟩))
        (ThetaStarBasis0 Θ (Fof s i)) =
      linM (ThetaStarBasis0 Θ)
        (bracketJBasis0 JmOmega (Sum.inl ⟨(u, v), h1⟩) (Fof s i)) := by
  change liftB B0data (∑ w : I n, ∑ z : I n, gtens (gmul (Θ u w) (Θ v z)) (eN (Lof w z)))
      (∑ a : I n, gtens (Θ s a) (eN (Fof a i))) = _
  simp only [liftB_sum_left, liftB_sum_right, liftB0_gtens_eN, parity_Lof, sigPow_zero,
    bracket0Basis_Lof_Fof, bracketLF, gtens_add_right, gtens_rsmul_right, Finset.sum_add_distrib]
  rw [bracketJBasis0_L_F]
  simp only [linM_rsmul, linM_add, linM_gtens_eN, T0_F]
  rw [shapeF1 Θ hΘ, shapeF2 Θ hEven hΘ, smul_add]

theorem HasParity.toEven {a : GR F n r} (h : HasParity 0 a) : IsEvenGR a := by
  intro T hT
  apply h T
  intro hc
  have := Nat.even_iff.mp (ZMod.natCast_eq_zero_iff_even.mp hc)
  omega

theorem IsEvenGR.gmul {a b : GR F n r} (ha : IsEvenGR a) (hb : IsEvenGR b) :
    IsEvenGR (gmul a b) := by
  have := ha.parity.gmul hb.parity
  rw [add_zero] at this
  exact this.toEven

theorem gmul_comm3 {c : GR F n r} (hc : IsEvenGR c) (A B : GR F n r) :
    gmul c (gmul A B) = gmul (gmul A B) c := by
  rw [← gmul_assoc, gmul_comm_of_even hc A, gmul_assoc, gmul_comm_of_even hc B, ← gmul_assoc]

theorem bracketJBasis0_F_L (J' : I n → I n → GR F n r) (u v w : I n) (h : Bmn.IKey u ≤ Bmn.IKey v)
    (i : F.K) :
    bracketJBasis0 J' (Fof w i) (Sum.inl ⟨(u, v), h⟩) =
      -((1 / 2 : ℚ) • (gtens (J' v w) (eN (Fof u i)) + gtens (J' u w) (eN (Fof v i)))) := rfl

theorem VecFL (Θ : I n → I n → GR F n r) (hEven : ∀ u w, IsEvenGR (Θ u w))
    (hΘ : ∀ u v, thetaJthetaT Θ u v = JR u v - OmegaR u v) (u v s : I n)
    (h1 : Bmn.IKey u ≤ Bmn.IKey v) (i : F.K) :
    liftB B0data (ThetaStarBasis0 Θ (Fof s i))
        (ThetaStarBasis0 Θ (Sum.inl ⟨(u, v), h1⟩)) =
      linM (ThetaStarBasis0 Θ)
        (bracketJBasis0 JmOmega (Fof s i) (Sum.inl ⟨(u, v), h1⟩)) := by
  change liftB B0data (∑ a : I n, gtens (Θ s a) (eN (Fof a i)))
      (∑ w : I n, ∑ z : I n, gtens (gmul (Θ u w) (Θ v z)) (eN (Lof w z))) = _
  simp only [liftB_sum_left, liftB_sum_right, liftB0_gtens_eN, parity_Fof, bracket0Basis_Fof_Lof,
    bracketLF, gtens_neg_right, gtens_add_right, gtens_rsmul_right, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  rw [bracketJBasis0_F_L]
  simp only [linM_neg, linM_rsmul, linM_add, linM_gtens_eN, T0_F]
  have hE : ∀ w z, IsEvenGR (gmul (Θ u w) (Θ v z)) := fun w z =>
    IsEvenGR.gmul (hEven u w) (hEven v z)
  simp only [sigPow_of_even 1 (hE _ _), gmul_comm3 (hEven s _)]
  have e1 := shapeF1 Θ hΘ u v s i
  have e2 := shapeF2 Θ hEven hΘ u v s i
  rw [sum_perm3] at e1 e2
  rw [e1, e2, smul_add]

theorem bracket0Basis_Fof_Fof (a : I n) (i : F.K) (b : I n) (j : F.K) :
    bracket0Basis (Fof a i : OspBasis F n) (Fof b j) = bracketFF a i b j := rfl

theorem bracketJBasis0_F_F (J' : I n → I n → GR F n r) (u v : I n) (i j : F.K) :
    bracketJBasis0 J' (Fof u i) (Fof v j) =
      (1 / 4 : ℚ) • gtens (J' u v) (Sof i j) + (1 / 2 * F.g i j) • gtens gone (eN (Lof u v)) :=
  rfl

theorem VecFF (Θ : I n → I n → GR F n r) (hEven : ∀ u w, IsEvenGR (Θ u w))
    (hΘ : ∀ u v, thetaJthetaT Θ u v = JR u v - OmegaR u v) (u v : I n) (i j : F.K) :
    liftB B0data (ThetaStarBasis0 Θ (Fof u i)) (ThetaStarBasis0 Θ (Fof v j)) =
      linM (ThetaStarBasis0 Θ) (bracketJBasis0 JmOmega (Fof u i) (Fof v j)) := by
  change liftB B0data (∑ a : I n, gtens (Θ u a) (eN (Fof a i)))
      (∑ b : I n, gtens (Θ v b) (eN (Fof b j))) = _
  have hs : ∀ b, sigPow 1 (Θ v b) = Θ v b := fun b => sigPow_of_even 1 (hEven v b)
  simp only [liftB_sum_left, liftB_sum_right, liftB0_gtens_eN, parity_Fof, hs,
    bracket0Basis_Fof_Fof, bracketFF, gtens_add_right, gtens_rsmul_right, Finset.sum_add_distrib]
  rw [bracketJBasis0_F_F]
  simp only [linM_rsmul, linM_add, linM_gtens', extT_Sof _ (ThetaStar_SCompat Θ), extT_eN,
    gsmul_gone, gsmul_gtens, gmul_gone, T0_Lof Θ hEven]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [Finset.sum_comm,
      sum_gtens_rat (fun a b => 1 / 4 * J n a b) (fun a b => gmul (Θ u a) (Θ v b)),
      gtens_rsmul_left]
    refine congrArg (fun q => gtens q (Sof i j)) ?_
    have h : ∑ a : I n, ∑ b : I n, (1 / 4 * J n a b) • gmul (Θ u a) (Θ v b) =
        (1 / 4 : ℚ) • JmOmega (F := F) (r := r) u v := by
      rw [← contract_basic_rat Θ hΘ u v, Finset.smul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun a _ => mul_smul _ _ _
    rw [h]
  · rw [Finset.smul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.smul_sum]

theorem bracket0_Sof_Fof (j k : F.K) (h : F.key j < F.key k) (a : I n) (i : F.K) :
    bracket0 (Sof j k : OspMod F n) (eN (Fof a i)) = bracketSF j k a i := by
  rw [Sof_of_lt h, bracket0_eN_eN]; rfl

theorem bracket0_Fof_Sof (a : I n) (i : F.K) (j k : F.K) (h : F.key j < F.key k) :
    bracket0 (eN (Fof a i) : OspMod F n) (Sof j k) = - bracketSF j k a i := by
  rw [Sof_of_lt h, bracket0_eN_eN]; rfl

theorem extT_bracketSF (Θ : I n → I n → GR F n r) (j k : F.K) (w : I n) (i : F.K) :
    extT (ThetaStarBasis0 Θ) (bracketSF j k w i : OspMod F n) =
      (F.g k i) • ∑ a : I n, gtens (Θ w a) (eN (Fof a j)) -
        (F.g j i) • ∑ a : I n, gtens (Θ w a) (eN (Fof a k)) := by
  unfold bracketSF
  rw [extT_sub, extT_rsmul, extT_rsmul, extT_eN, extT_eN]
  rfl

theorem VecSF (Θ : I n → I n → GR F n r) (j k : F.K) (h : F.key j < F.key k) (w : I n)
    (i : F.K) :
    liftB B0data (ThetaStarBasis0 Θ (Sum.inr (Sum.inl ⟨(j, k), h⟩)))
        (ThetaStarBasis0 Θ (Fof w i)) =
      linM (ThetaStarBasis0 Θ)
        (bracketJBasis0 JmOmega (Sum.inr (Sum.inl ⟨(j, k), h⟩)) (Fof w i)) := by
  change liftB B0data (gtens gone (Sof j k)) (∑ a : I n, gtens (Θ w a) (eN (Fof a i))) =
    linM (ThetaStarBasis0 Θ) (gtens gone (bracketSF j k w i))
  simp only [liftB_sum_right, liftB0_gtens _ _ _ _ 0 (hv_Sof j k), sigPow_zero, gone_gmul,
    bracket0_Sof_Fof j k h, linM_gtens', extT_bracketSF, gsmul_gone]
  unfold bracketSF
  simp only [gtens_sub_right, gtens_rsmul_right, Finset.sum_sub_distrib, Finset.smul_sum]

theorem HasCard.isEven_zero {a : GR F n r} (ha : HasCard 0 a) : IsEvenGR a :=
  ha.isEven (by norm_num)

theorem VecFS (Θ : I n → I n → GR F n r) (j k : F.K) (h : F.key j < F.key k) (w : I n)
    (i : F.K) :
    liftB B0data (ThetaStarBasis0 Θ (Fof w i))
        (ThetaStarBasis0 Θ (Sum.inr (Sum.inl ⟨(j, k), h⟩))) =
      linM (ThetaStarBasis0 Θ)
        (bracketJBasis0 JmOmega (Fof w i) (Sum.inr (Sum.inl ⟨(j, k), h⟩))) := by
  change liftB B0data (∑ a : I n, gtens (Θ w a) (eN (Fof a i))) (gtens gone (Sof j k)) =
    linM (ThetaStarBasis0 Θ) (- gtens gone (bracketSF j k w i))
  have hg : ∀ π : ZMod 2, sigPow π (gone : GR F n r) = gone := fun π =>
    sigPow_of_even π (HasCard_gone (F := F) (n := n) (r := r)).isEven_zero
  have hl : ∀ a : I n, liftB B0data (gtens (Θ w a) (eN (Fof a i))) (gtens gone (Sof j k)) =
      gtens (gmul (Θ w a) (sigPow 1 gone)) (bracket0 (eN (Fof a i)) (Sof j k)) :=
    fun a => liftB0_gtens _ _ _ _ 1 (hv_Fof a i)
  rw [liftB_sum_left]
  simp only [hl, hg, gmul_gone, bracket0_Fof_Sof _ _ j k h, gtens_neg_right, linM_neg,
    linM_gtens', extT_bracketSF, gsmul_gone, Finset.sum_neg_distrib]
  unfold bracketSF
  simp only [gtens_sub_right, gtens_rsmul_right, Finset.sum_sub_distrib, Finset.smul_sum]

theorem thetaStar_bracket' (Θ : I n → I n → GR F n r) (hEven : ∀ u w, IsEvenGR (Θ u w))
    (hΘ : ∀ u v, thetaJthetaT Θ u v = JR u v - OmegaR u v) (x y : RModM F n r) :
    bracket0M (ThetaStar Θ x) (ThetaStar Θ y) = ThetaStar Θ (bracketJM JmOmega x y) := by
  rw [ThetaStar_eq_linM, bracketJM_eq_liftB, bracket0M_eq_liftB]
  refine lift_intertwine_vec (ThetaStarBasis0 Θ) (ThetaStarBasis0 Θ) B0data
    (bracketJBasis0 JmOmega) (ThetaStar_parity Θ hEven) (fun Z Z' => ?_) x y
  rcases Z with ⟨⟨u, v⟩, h1⟩ | ⟨⟨i, j⟩, h1⟩ | ⟨s, i⟩ <;>
  rcases Z' with ⟨⟨a, b⟩, h2⟩ | ⟨⟨k, l⟩, h2⟩ | ⟨t, m⟩
  · exact VecLL Θ hEven hΘ u v a b h1 h2
  · exact VecLS Θ u v h1 k l h2
  · exact VecLF Θ hEven hΘ u v t h1 m
  · exact VecSL Θ a b h2 i j h1
  · exact VecSS Θ i j k l h1 h2
  · exact VecSF Θ i j h1 t m
  · exact VecFL Θ hEven hΘ a b s h2 i
  · exact VecFS Θ k l h2 s i
  · exact VecFF Θ hEven hΘ s t i m

end Multi
end OspN
end OspOddDeformations
