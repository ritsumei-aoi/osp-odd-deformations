import OspOddDeformations.OspN.Presented.Recovery
import OspOddDeformations.OspN.Presented.MultiRecovery

/-!
# `[·,·]_β` is the supercommutator of the lifts on all of `𝔤_R`

The paper defines `[·,·]_β` on `𝔤_R` by `ι_β([X,Y]_β) = [ι_β X, ι_β Y]` (§4.1), extended from basis
elements because `ι_β` is `R`-linear and the scalars are central. The coefficients `P` (resp. `P_r`)
are even and central, so it is enough to take `X`, `Y` in a homogeneous `P`-basis of `𝔤_R`; the
brackets on both sides are `P`-bilinear by definition.

* One odd parameter: the `P`-basis of `𝔤_R` is `X` and `κX` (`eR (X, false)`, `eR (X, true)`), of
  parities `p(X)` and `p(X) + 1`; `scommR_eR` gives the supercommutator of their lifts as `ι_β`
  of the development's `[·,·]_β` (`bracketRBetaBasis`), from `recovery` and `κX̂ = (−1)^{p(X)} X̂κ`
  in `A_β`.
* `r` odd parameters: for homogeneous `x`, `y ∈ 𝔤_{R_r}` (`HomM`), `scommM_homog` gives the
  supercommutator of `ι_β x`, `ι_β y` as `ι_β([x,y]_β)` with the bracket (5.3), through `Φ_r`, the
  parity of `U` and `iota0_scomm`.
-/

namespace OspOddDeformations
namespace OspN
namespace Presented

open Bmn (I J)

/-! ## One odd parameter -/

section single

variable (F : FermionIndex) (n : ℕ)

theorem κP_mul_XhatP (X : OspBasis F n) :
    κP F n * XhatP F n X = gsign 1 (OspN.parity X) • (XhatP F n X * κP F n) := by
  have hXeq : XhatP F n X = X0P F n X + κP F n * iota0P F n (hTildeBasis X) := by
    rw [XhatP_eq, iota0_eN, hTilde_eN]
  have hXhom : ∀ Z : OspBasis F n, hTildeBasis X Z ≠ 0 → OspN.parity Z = OspN.parity X + 1 :=
    fun Z hZ => by
      by_contra hne; exact hZ (hTildeBasis_apply_eq_zero_of_parity_ne X Z hne)
  set A := X0P F n X
  set a := iota0P F n (hTildeBasis X)
  have hκa : κP F n * a = gsign 1 (OspN.parity X + 1) • (a * κP F n) :=
    κP_comm_iota0_homog (OspN.parity X + 1) (hTildeBasis X) hXhom
  have haκ : a * κP F n = gsign 1 (OspN.parity X + 1) • (κP F n * a) := by
    rw [hκa, smul_smul, gsign_sq, one_smul]
  have hκκ : κP F n * κP F n = 0 := κP_sq F n
  rw [hXeq, mul_add, ← mul_assoc, hκκ, zero_mul, add_zero, add_mul, mul_assoc, haκ,
    mul_smul_comm, ← mul_assoc, hκκ, zero_mul, smul_zero, add_zero, κP_comm_X0]

/-- In `A_β`: `κ X̂ = (−1)^{p(X)} X̂ κ`. -/
theorem κB_mul_Xp (X : OspBasis F n) :
    κB F n * Xp (beta F n) X = gsign 1 (OspN.parity X) • (Xp (beta F n) X * κB F n) := by
  apply (untwist F n).injective
  rw [map_mul, untwist_rat_smul, map_mul, untwist_κB, untwist_Xp, κP_mul_XhatP]

theorem Xp_mul_κB (X : OspBasis F n) :
    Xp (beta F n) X * κB F n = gsign 1 (OspN.parity X) • (κB F n * Xp (beta F n) X) := by
  rw [κB_mul_Xp, smul_smul, gsign_sq, one_smul]

theorem iotaP_eN (β' : I n → F.K → Pmn F n) (X : OspBasis F n) :
    iotaP β' (eN X) = Xp β' X := by
  simp [iotaP, eN, ite_smul, Finset.sum_ite_eq']

theorem iotaP_zero' (β' : I n → F.K → Pmn F n) : iotaP (F := F) (n := n) β' 0 = 0 := by
  simp [iotaP]

theorem iotaP_rsmul (β' : I n → F.K → Pmn F n) (c : ℚ) (x : OspMod F n) :
    iotaP β' (c • x) = c • iotaP β' x := by
  simp only [iotaP, Finset.smul_sum]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [Pi.smul_apply, smul_assoc]

theorem iotaRP_eR_false (X : OspBasis F n) :
    iotaRP (beta F n) (eR ((X, false) : RBasis F n)) = Xp (beta F n) X := by
  have ht : truePart (eR ((X, false) : RBasis F n)) = 0 := by
    funext k; simp [truePart, eR]
  rw [iotaRP, falsePart_eR_false, ht, iotaP_eN, iotaP_zero', mul_zero, add_zero]

theorem iotaRP_eR_true (X : OspBasis F n) :
    iotaRP (beta F n) (eR ((X, true) : RBasis F n)) = κB F n * Xp (beta F n) X := by
  have ht : truePart (eR ((X, true) : RBasis F n)) = eN X := by
    funext k; simp [truePart, eR, eN, Prod.ext_iff]
  rw [iotaRP, falsePart_eR_true, ht, iotaP_eN, iotaP_zero', zero_add]

theorem iotaRP_iotaR_add_kappaEmbed (v w : OspMod F n) :
    iotaRP (beta F n) (iotaR v + kappaEmbed w)
      = iotaP (beta F n) v + κB F n * iotaP (beta F n) w := by
  have hf : falsePart (iotaR v + kappaEmbed w) = v := by
    funext i; simp [falsePart, iotaR, kappaEmbed]
  have ht : truePart (iotaR v + kappaEmbed w) = w := by
    funext i; simp [truePart, iotaR, kappaEmbed]
  rw [iotaRP, hf, ht]

theorem iotaRP_kappaEmbed (w : OspMod F n) :
    iotaRP (beta F n) (kappaEmbed w) = κB F n * iotaP (beta F n) w := by
  have h := iotaRP_iotaR_add_kappaEmbed F n 0 w
  have h0 : iotaR (0 : OspMod F n) = 0 := by funext i; simp [iotaR]
  rwa [h0, zero_add, iotaP_zero', zero_add] at h

end single

/-! Three identities in any ring, for `k` with `k² = 0` that (super)commutes with `a` and `b`. -/

section alg

variable {A : Type*} [Ring A] [Algebra ℚ A] {a b k : A} {gx gy : ℚ}

theorem alg_tf (hbk : b * k = gy • (k * b)) (s s' : ℚ) (hs : s' * gy = s) :
    k * a * b - s' • (b * (k * a)) = k * (a * b - s • (b * a)) := by
  rw [← mul_assoc b, hbk, smul_mul_assoc, smul_smul, hs, mul_sub, mul_smul_comm, mul_assoc,
    mul_assoc]

theorem alg_ft (hak : a * k = gx • (k * a)) (s s' : ℚ) (hs : s' = s * gx) :
    a * (k * b) - s' • (k * b * a) = gx • (k * (a * b - s • (b * a))) := by
  rw [← mul_assoc a, hak, smul_mul_assoc, hs, mul_sub, mul_smul_comm, smul_sub, smul_smul,
    mul_comm gx s, ← smul_smul, mul_assoc, mul_assoc, smul_smul]

theorem alg_tt (hak : a * k = gx • (k * a)) (hbk : b * k = gy • (k * b)) (hkk : k * k = 0)
    (c : ℚ) : k * a * (k * b) - c • (k * b * (k * a)) = 0 := by
  have h1 : k * a * (k * b) = 0 := by
    rw [mul_assoc, ← mul_assoc a, hak, smul_mul_assoc, mul_smul_comm, ← mul_assoc, ← mul_assoc,
      hkk, zero_mul, zero_mul, smul_zero]
  have h2 : k * b * (k * a) = 0 := by
    rw [mul_assoc, ← mul_assoc b, hbk, smul_mul_assoc, mul_smul_comm, ← mul_assoc, ← mul_assoc,
      hkk, zero_mul, zero_mul, smul_zero]
  rw [h1, h2, smul_zero, sub_zero]

end alg

section single

variable (F : FermionIndex) (n : ℕ)

/-- The parity of a `P`-basis element of `𝔤_R`: `p(X)` for `X`, `p(X) + 1` for `κX`. -/
def parR (p : RBasis F n) : ZMod 2 := OspN.parity p.1 + (if p.2 then 1 else 0)

/-- **`[·,·]_β` on `𝔤_R`** (§4.1), one odd parameter: for all `P`-basis elements `p`, `q` of
`𝔤_R` (`X` or `κX`), the supercommutator of `ι_β p` and `ι_β q` is `ι_β` of the development's
`[p,q]_β`. -/
theorem scommR_eR (p q : RBasis F n) :
    iotaRP (beta F n) (eR p) * iotaRP (beta F n) (eR q)
        - gsign (parR F n p) (parR F n q) • (iotaRP (beta F n) (eR q) * iotaRP (beta F n) (eR p))
      = iotaRP (beta F n) (bracketRBetaBasis p q) := by
  obtain ⟨X, bX⟩ := p
  obtain ⟨Y, bY⟩ := q
  have hrec := recovery F n X Y
  unfold scomm at hrec
  have hkrec : κB F n * (Xp (beta F n) X * Xp (beta F n) Y
      - gsign (OspN.parity X) (OspN.parity Y) • (Xp (beta F n) Y * Xp (beta F n) X))
      = κB F n * iotaP (beta F n) (bracket0Basis X Y) := by
    rw [hrec, mul_add, ← mul_assoc, κ_mul_κ, zero_mul, add_zero]
  have hak := Xp_mul_κB F n X
  have hbk := Xp_mul_κB F n Y
  cases bX <;> cases bY <;>
    simp only [parR, Bool.false_eq_true, ↓reduceIte, add_zero, iotaRP_eR_false, iotaRP_eR_true,
      bracketRBetaBasis]
  · rw [iotaRP_iotaR_add_kappaEmbed]; exact hrec
  · rw [alg_ft hak _ _ (by rw [gsign_symm, gsign_shift_left, gsign_symm (OspN.parity Y),
      gsign_symm 1]), hkrec, iotaRP_kappaEmbed, iotaP_rsmul, mul_smul_comm, gsign_symm 1]
  · rw [alg_tf hbk _ _ (by rw [gsign_shift_left, mul_assoc, gsign_sq, mul_one]), hkrec,
      iotaRP_kappaEmbed]
  · rw [alg_tt hak hbk κ_mul_κ]
    symm
    simp [iotaRP, falsePart, truePart, iotaP]

end single

/-! ## `r` odd parameters -/

section multi

variable {F : FermionIndex} {n r : ℕ}

theorem HomM_gsmul_gmono {q : ZMod 2} {w : Multi.RModM F n r} (S : Finset (Fin r))
    (hw : HomM q w) : HomM ((S.card : ZMod 2) + q) (Multi.gsmul (Multi.gmono S 1) w) := by
  rintro ⟨W, T⟩ hne
  by_contra hpar
  apply hne
  simp only [Multi.gsmul, Multi.gmono]
  refine Finset.sum_eq_zero fun A _ => Finset.sum_eq_zero fun B _ => ?_
  by_cases hU : A ∪ B = T
  · by_cases hA : A = S
    · subst hA
      by_cases hd : Disjoint A B
      · by_cases hwB : w (W, B) = 0
        · simp [hwB]
        · exfalso
          apply hpar
          have h1 := hw (W, B) hwB
          simp only [parB] at h1 ⊢
          rw [← hU, Finset.card_union_of_disjoint hd, Nat.cast_add, ← h1]
          ring
      · simp [Multi.gs_eq_zero_of_not_disjoint hd]
    · simp [hA]
  · simp [hU]

/-- `U` preserves the parity of homogeneous elements of `𝔤_{R_r}`. -/
theorem HomM_UM {p : ZMod 2} {x : Multi.RModM F n r} (hx : HomM p x) :
    HomM p (Multi.UM Multi.thetaSeries x) := by
  intro P hP
  by_contra hpar
  apply hP
  simp only [Multi.UM, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun Q _ => ?_
  by_cases hxQ : x Q = 0
  · simp [hxQ]
  · have hQ := hx Q hxQ
    have hU : HomM (OspN.parity Q.1) (Multi.UBasis0 (r := r) Multi.thetaSeries Q.1) := by
      have := HomM_UM_eM (F := F) (n := n) (r := r) Q.1
      rwa [A7b.UM_eM] at this
    have h := HomM_gsmul_gmono Q.2 hU
    have hzero : Multi.gsmul (Multi.gmono Q.2 1) (Multi.UBasis0 Multi.thetaSeries Q.1) P = 0 := by
      by_contra hne
      apply hpar
      rw [h P hne, ← hQ, parB, add_comm]
    rw [hzero, mul_zero]

/-- **Thm 5.3 on all of `𝔤_{R_r}`**: for homogeneous `x`, `y`, the supercommutator of `ι_β x` and
`ι_β y` is `ι_β([x,y]_β)`, with `[·,·]_β` given by (5.3). -/
theorem scommM_homog {p q : ZMod 2} {x y : Multi.RModM F n r} (hx : HomM p x) (hy : HomM q y) :
    iotaM (Multi.betaR F n r) x * iotaM (Multi.betaR F n r) y
        - gsign p q • (iotaM (Multi.betaR F n r) y * iotaM (Multi.betaR F n r) x)
      = iotaM (Multi.betaR F n r) (Multi.bracketBetaM x y) := by
  apply (untwistR F n r).injective
  rw [map_sub, map_mul, untwistR_rat_smul, map_mul, untwistR_iotaM, untwistR_iotaM,
    untwistR_iotaM, iota0_scomm (HomM_UM hx) (HomM_UM hy), Multi.intertwining_thetaSeries]

end multi

end Presented
end OspN
end OspOddDeformations
