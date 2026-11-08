import OspOddDeformations.OspN.Special
import OspOddDeformations.OspN.Coboundary

/-!
# Remark 6.2: the Killing form of `osp(4|2)`, and its superdimension

* The Killing (super)form `K(x,y) = str(ad x ∘ ad y)` of `osp(4|2)` vanishes
  (`d21_killing_zero`). The structure constants are integers over `4` (`c4`, a computable copy
  of `bracket0Basis` times `4`, `bracket0Basis_eq_c4`), and `K` on basis pairs is evaluated by
  the kernel (`decide +kernel`, `d21_K16_zero`).
* `osp(4|2)` is the only `osp(N|2n)` of superdimension `(9|8)` (`sdim_9_8_iff`), from the
  counts `2·dim 𝔤₀̄ = 2n(2n+1) + N(N−1)`, `dim 𝔤₁̄ = 2nN`.
-/

-- As in `FBeta.lean`: `OspBasis` is a plain `def` whose sum structure the proofs use.
set_option backward.isDefEq.respectTransparency.types false

namespace OspOddDeformations
namespace OspN
namespace GroupB

open Bmn (I J IKey)

variable {F : FermionIndex} {n : ℕ}

/-! ## A computable copy of the structure constants, times `4` -/

/-- A computable decidable equality on the basis (`OspBasis`'s own instance is classical). -/
def decB : DecidableEq (OspBasis F n) := by
  unfold OspBasis
  have : DecidableEq F.K := F.dec
  exact instDecidableEqSum

def eZ (b k : OspBasis F n) : ℤ := @ite _ (k = b) (decB k b) 1 0

def JZ (n : ℕ) : I n → I n → ℤ
  | (k1, false), (k2, true) => if k1 = k2 then 1 else 0
  | (k1, true), (k2, false) => if k1 = k2 then -1 else 0
  | _, _ => 0

def gZ (F : FermionIndex) (i j : F.K) : ℤ := if j = F.dual i then 1 else 0

def SofZ (i j : F.K) (k : OspBasis F n) : ℤ :=
  if h : F.key i < F.key j then eZ (Sum.inr (Sum.inl ⟨(i, j), h⟩)) k
  else if h2 : F.key j < F.key i then -eZ (Sum.inr (Sum.inl ⟨(j, i), h2⟩)) k
  else 0

def LL4 (u v w z : I n) (k : OspBasis F n) : ℤ :=
  2 * JZ n v w * eZ (Lof u z) k + 2 * JZ n u w * eZ (Lof v z) k
  + 2 * JZ n v z * eZ (Lof u w) k + 2 * JZ n u z * eZ (Lof v w) k

def SS4 (i j k l : F.K) (m : OspBasis F n) : ℤ :=
  4 * (gZ F j k * SofZ i l m - gZ F i k * SofZ j l m - gZ F j l * SofZ i k m
    + gZ F i l * SofZ j k m)

def LF4 (u v w : I n) (i : F.K) (k : OspBasis F n) : ℤ :=
  2 * JZ n v w * eZ (Fof u i) k + 2 * JZ n u w * eZ (Fof v i) k

def SF4 (j k : F.K) (w : I n) (i : F.K) (m : OspBasis F n) : ℤ :=
  4 * (gZ F k i * eZ (Fof w j) m - gZ F j i * eZ (Fof w k) m)

def FF4 (u : I n) (i : F.K) (v : I n) (j : F.K) (k : OspBasis F n) : ℤ :=
  JZ n u v * SofZ i j k + 2 * gZ F i j * eZ (Lof u v) k

/-- `4 ×` the structure constants `bracket0Basis X Y k`, computably. -/
def c4 : OspBasis F n → OspBasis F n → OspBasis F n → ℤ
  | .inl ⟨(u, v), _⟩, .inl ⟨(w, z), _⟩ => LL4 u v w z
  | .inl _, .inr (.inl _) => 0
  | .inl ⟨(u, v), _⟩, .inr (.inr (w, i)) => LF4 u v w i
  | .inr (.inl _), .inl _ => 0
  | .inr (.inl ⟨(i, j), _⟩), .inr (.inl ⟨(k, l), _⟩) => SS4 i j k l
  | .inr (.inl ⟨(j, k), _⟩), .inr (.inr (w, i)) => SF4 j k w i
  | .inr (.inr (w, i)), .inl ⟨(u, v), _⟩ => fun m => -LF4 u v w i m
  | .inr (.inr (w, i)), .inr (.inl ⟨(j, k), _⟩) => fun m => -SF4 j k w i m
  | .inr (.inr (u, i)), .inr (.inr (v, j)) => FF4 u i v j

/-- The sign `(-1)^{p(k)}`. -/
def sgnZ : OspBasis F n → ℤ
  | .inl _ => 1
  | .inr (.inl _) => 1
  | .inr (.inr _) => -1

/-- `16 K(e_a, e_i) = 16 Σ_k (-1)^{p(k)} Σ_l c_{ik}^l c_{al}^k`. -/
def K16 (a i : OspBasis F n) : ℤ := ∑ k, sgnZ k * ∑ l, c4 i k l * c4 a l k

/-! ## The copy is the structure constants -/

theorem eN_apply_eZ (b k : OspBasis F n) : eN b k = algebraMap ℚ (Pmn F n) (eZ b k) := by
  unfold eN eZ
  by_cases h : k = b <;> simp [h]

theorem Sof_apply_SofZ (i j : F.K) (k : OspBasis F n) :
    Sof i j k = algebraMap ℚ (Pmn F n) (SofZ i j k) := by
  unfold Sof SofZ
  split_ifs <;> simp only [Pi.neg_apply, eN_apply_eZ, Int.cast_neg, map_neg, Int.cast_zero,
    map_zero, Pi.zero_apply]

theorem J_eq_JZ (u v : I n) : J n u v = (JZ n u v : ℚ) := by
  rcases u with ⟨k1, b1⟩
  rcases v with ⟨k2, b2⟩
  cases b1 <;> cases b2 <;> simp only [J, JZ] <;> (try split_ifs) <;> simp

theorem g_eq_gZ (i j : F.K) : F.g i j = (gZ F i j : ℚ) := by
  unfold FermionIndex.g gZ; split_ifs <;> simp

theorem bracket0Basis_eq_c4 (X Y k : OspBasis F n) :
    bracket0Basis X Y k = algebraMap ℚ (Pmn F n) ((c4 X Y k : ℚ) / 4) := by
  rcases X with ⟨⟨u, v⟩, _⟩ | ⟨⟨i, j⟩, _⟩ | ⟨u, i⟩ <;>
    rcases Y with ⟨⟨w, z⟩, _⟩ | ⟨⟨k', l⟩, _⟩ | ⟨w, j'⟩ <;>
    simp only [bracket0Basis, c4, bracketLL, bracketLF, bracketSS, bracketSF, bracketFF, LL4,
      LF4, SS4, SF4, FF4, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
      Pi.zero_apply] <;>
    simp only [eN_apply_eZ, Sof_apply_SofZ, J_eq_JZ, g_eq_gZ, Algebra.smul_def, ← map_mul,
      ← map_add, ← map_sub, ← map_neg, ← map_zero (algebraMap ℚ (Pmn F n))] <;>
    congr 1 <;> push_cast <;> ring

/-! ## The Killing form -/

/-- The Killing (super)form `K(x,y) = str(ad x ∘ ad y)` on `𝔤_P`, in the homogeneous basis. -/
noncomputable def killing0 (x y : OspMod F n) : Pmn F n :=
  ∑ k, ((sgnZ k : ℤ) : ℚ) • bracket0 x (bracket0 y (eN k)) k

theorem killing0_eq (x y : OspMod F n) :
    killing0 x y = ∑ a, ∑ i, x a * y i * algebraMap ℚ (Pmn F n) ((K16 a i : ℚ) * (1 / 16)) := by
  have hc : ∀ X Y k : OspBasis F n, bracket0Basis X Y k
      = algebraMap ℚ (Pmn F n) (c4 X Y k : ℚ) * algebraMap ℚ (Pmn F n) (1 / 4) := by
    intro X Y k; rw [bracket0Basis_eq_c4, ← map_mul, div_eq_mul_one_div]
  have h16 : algebraMap ℚ (Pmn F n) (1 / 16) = algebraMap ℚ (Pmn F n) (1 / 4)
      * algebraMap ℚ (Pmn F n) (1 / 4) := by rw [← map_mul]; norm_num
  unfold killing0 K16
  simp only [bracket0_eN_right]
  simp only [bracket0, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [hc, h16, Algebra.smul_def, Int.cast_sum, Int.cast_mul, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

/-- `16 K` vanishes on all basis pairs of `osp(4|2)`, by evaluation in the kernel. -/
theorem d21_K16_zero : ∀ a i : OspBasis (evenIdx 2) 1, K16 a i = 0 := by
  decide +kernel

/-- **Remark 6.2**: the Killing form of `osp(4|2) = D(2,1)` vanishes. -/
theorem d21_killing_zero (x y : OspMod (evenIdx 2) 1) : killing0 x y = 0 := by
  rw [killing0_eq]
  simp [d21_K16_zero]

/-! ## The superdimension -/

/-- `dim 𝔤₀̄`. -/
def evenCard (F : FermionIndex) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun X : OspBasis F n => parity X = 0).card

/-- `dim 𝔤₁̄`. -/
def oddCard (F : FermionIndex) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun X : OspBasis F n => parity X = 1).card

/-- Pairs ordered by an injective key: `2·#{f a < f b} + m = m²` and
`#{f a ≤ f b} = #{f a < f b} + m`. -/
theorem card_key_pairs {α : Type*} [Fintype α] (f : α → ℕ) (hf : Function.Injective f) :
    2 * Fintype.card {p : α × α // f p.1 < f p.2} + Fintype.card α
        = Fintype.card α * Fintype.card α ∧
      Fintype.card {p : α × α // f p.1 ≤ f p.2}
        = Fintype.card {p : α × α // f p.1 < f p.2} + Fintype.card α := by
  classical
  simp only [Fintype.card_subtype]
  have hB : (Finset.univ.filter fun p : α × α => f p.2 < f p.1).card
      = (Finset.univ.filter fun p : α × α => f p.1 < f p.2).card :=
    Finset.card_bij (fun p _ => p.swap) (by simp) (by simp)
      (fun b hb => ⟨b.swap, by simpa using hb, by simp⟩)
  have hD : (Finset.univ.filter fun p : α × α => p.1 = p.2).card = Fintype.card α := by
    rw [show (Finset.univ.filter fun p : α × α => p.1 = p.2)
        = Finset.univ.image (fun a => (a, a)) by ext ⟨a, b⟩; simp [eq_comm],
      Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), Finset.card_univ]
  have htri : ∀ p : α × α, f p.1 < f p.2 ∨ f p.2 < f p.1 ∨ p.1 = p.2 := by
    intro p
    rcases lt_trichotomy (f p.1) (f p.2) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (hf h))
    · exact Or.inr (Or.inl h)
  constructor
  · have hU : (Finset.univ.filter fun p : α × α => f p.1 < f p.2).card
        + (Finset.univ.filter fun p : α × α => f p.2 < f p.1).card
        + (Finset.univ.filter fun p : α × α => p.1 = p.2).card
        = Fintype.card α * Fintype.card α := by
      rw [← Fintype.card_prod, ← Finset.card_univ, Finset.card_filter, Finset.card_filter,
        Finset.card_filter, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        Finset.card_eq_sum_ones]
      refine Finset.sum_congr rfl fun p _ => ?_
      rcases htri p with h | h | h
      · have h1 : ¬ f p.2 < f p.1 := by omega
        have h2 : p.1 ≠ p.2 := fun e => by rw [e] at h; omega
        simp [h, h1, h2]
      · have h1 : ¬ f p.1 < f p.2 := by omega
        have h2 : p.1 ≠ p.2 := fun e => by rw [e] at h; omega
        simp [h, h1, h2]
      · simp [h]
    omega
  · rw [← hD, Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases htri p with h | h | h
    · have h2 : p.1 ≠ p.2 := fun e => by rw [e] at h; omega
      simp [h, h.le, h2]
    · have h1 : ¬ f p.1 ≤ f p.2 := by omega
      have h2 : p.1 ≠ p.2 := fun e => by rw [e] at h; omega
      simp [h1, h2, show ¬ f p.1 < f p.2 by omega]
    · simp [h]

theorem IKey_injective : Function.Injective (IKey (n := n)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  cases b <;> cases d <;> simp [IKey, Fin.ext_iff] at h ⊢ <;> omega

theorem oddCard_eq : oddCard F n = 2 * n * Fintype.card F.K := by
  have h : (Finset.univ : Finset (I n × F.K)).card
      = (Finset.univ.filter fun X : OspBasis F n => parity X = 1).card := by
    refine Finset.card_bij (fun p _ => (Sum.inr (Sum.inr p) : OspBasis F n)) (by simp [parity])
      (fun a _ b _ h => Sum.inr_injective (Sum.inr_injective h)) (fun b hb => ?_)
    rcases b with a | a | a <;> simp [parity] at hb ⊢
  rw [oddCard, ← h, Finset.card_univ, Fintype.card_prod]
  simp [mul_comm]

theorem card_OspBasis : Fintype.card (OspBasis F n)
    = Fintype.card {p : I n × I n // IKey p.1 ≤ IKey p.2}
      + Fintype.card {p : F.K × F.K // F.key p.1 < F.key p.2} + Fintype.card (I n × F.K) := by
  rw [show Fintype.card (OspBasis F n) = Fintype.card ({p : I n × I n // IKey p.1 ≤ IKey p.2}
      ⊕ {p : F.K × F.K // F.key p.1 < F.key p.2} ⊕ (I n × F.K)) from
    Fintype.card_congr (Equiv.refl _)]
  simp only [Fintype.card_sum, add_assoc]

theorem evenCard_add_oddCard : evenCard F n + oddCard F n = Fintype.card (OspBasis F n) := by
  have hc : ∀ p : ZMod 2, ¬ p = 0 ↔ p = 1 := by decide
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (OspBasis F n)))
    (fun X => parity X = 0)
  rw [Finset.card_univ] at h
  rw [← h, evenCard, oddCard]
  simp only [hc]

/-- `2·dim 𝔤₀̄ = 2n(2n+1) + N(N−1)` and `dim 𝔤₁̄ = 2nN`, with `N = |K|`. -/
theorem sdim_formula :
    2 * evenCard F n + Fintype.card F.K = 2 * n * (2 * n + 1) + Fintype.card F.K * Fintype.card F.K
      ∧ oddCard F n = 2 * n * Fintype.card F.K := by
  obtain ⟨hI1, hI2⟩ := card_key_pairs (IKey (n := n)) IKey_injective
  obtain ⟨hK1, -⟩ := card_key_pairs F.key F.key_injective
  have hI : Fintype.card (I n) = 2 * n := by simp [mul_comm]
  have hsum := evenCard_add_oddCard (F := F) (n := n)
  rw [card_OspBasis, oddCard_eq, Fintype.card_prod, hI] at hsum
  rw [hI] at hI1 hI2
  refine ⟨?_, oddCard_eq⟩
  nlinarith

/-- **Remark 6.2**: `osp(N|2n)` has superdimension `(9|8)` exactly for `N = 4`, `n = 1`. -/
theorem sdim_9_8_iff :
    (evenCard F n = 9 ∧ oddCard F n = 8) ↔ (Fintype.card F.K = 4 ∧ n = 1) := by
  obtain ⟨h1, h2⟩ := sdim_formula (F := F) (n := n)
  set N := Fintype.card F.K
  constructor
  · rintro ⟨he, ho⟩
    rw [ho] at h2
    have hnN : n * N = 4 := by linarith
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h] at hnN
      · exact h
    have hN0 : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · simp [h] at hnN
      · exact h
    have hn : n ≤ 4 := by nlinarith
    have hN : N ≤ 4 := by nlinarith
    clear_value N
    interval_cases n <;> interval_cases N <;> omega
  · rintro ⟨hN, rfl⟩
    rw [hN] at h1 h2
    omega

end GroupB
end OspN
end OspOddDeformations
