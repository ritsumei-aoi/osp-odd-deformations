import OspOddDeformations.OspN.Identification

/-!
# The `C(2)` control

The even instance at its smallest case, `evenIdx 1` with `n = 1` (`C(2) = osp(2|2)`, `N = 2`):
the basis has `8` elements, and three values of `Γ_β` (paper Proposition 4.4) are evaluated. They
agree with an exact computation of the bracket in `A_β`, made outside this development. -/

namespace OspOddDeformations
namespace OspN

open Bmn (I)

/-- The basis of the even instance at the smallest nontrivial case, `m = n = 1`
(`C(2) = osp(2|2)`), has cardinality `n(2n+1) + m(2m-1) + 2nN` (`N = 2m`, no self-dual fermion
index, unlike the odd case's `+1`) `= 3 + 1 + 4 = 8`, computed by `decide`. -/
theorem evenIdx_basis_card_1_1 :
    Fintype.card (OspBasis (evenIdx 1) 1) = 8 := by decide

/-! ## Three values of `Γ_β` at `C(2)`

`evenIdx 1` at `n = 1` is `C(2) = osp(2|2)`, `N = 2`, the smallest nontrivial even case, matching
`evenIdx_basis_card_1_1` above. The values below are checked at three of the four nontrivial
kinds of the `Γ_β` rule (`LS`, `SF`, `FF`; `LF` is the least index-sensitive of the four). In the
external computation the fermion labels are `{1,2}` (1-based, `dual(1)=2`, adjacent pairing) and
the bosons `{0,1}` (0-based); they correspond to `evenIdx 1`'s `F.K = Fin 1 × Bool` by
`key 0 = (0,false) ↔ 1`, `key 1 = (0,true) ↔ 2` (the adjacent pairing `evenIdx` uses, the literal
reading of the notation `K_N`). The three checks reproduce the external values term for term,
confirming that the `dual`/`g`/`key` fields of `evenIdx` represent `N = 2` as the paper intends,
not merely that `Gamma_eq_delta_hTilde_basis` holds for *some* internally consistent but
possibly mislabelled structure. -/

noncomputable def evenC2 : FermionIndex := evenIdx 1
/-- `evenIdx 1`'s two fermion basis elements, corresponding to the external labels `1`, `2`. -/
def evenC2_i0 : evenC2.K := (0, false)
def evenC2_i1 : evenC2.K := (0, true)
/-- `evenIdx 1` at `n = 1`'s two boson basis elements, corresponding to the external
labels `0`, `1` (the boson side is `Bmn`'s, independent of the fermion index). -/
def evenC2_u0 : I 1 := (0, false)
def evenC2_u1 : I 1 := (0, true)

/-- **The `SF` kind, at `evenIdx 1`, `n = 1`.** External value:
`Γ(S_{1,2}, F_{0,1}) = ½β_{0,1}·S_{1,2}`. -/
theorem evenC2_GammaBasis_SF :
    GammaBasis (F := evenC2) (n := 1) (Sum.inr (Sum.inl ⟨(evenC2_i0, evenC2_i1), by decide⟩))
        (Fof evenC2_u0 evenC2_i0)
      = (1 / 2 : ℚ) • (beta evenC2 1 evenC2_u0 evenC2_i0 • Sof evenC2_i0 evenC2_i1) := by
  change GammaSF evenC2_i0 evenC2_i1 evenC2_u0 evenC2_i0
      = (1 / 2 : ℚ) • (beta evenC2 1 evenC2_u0 evenC2_i0 • Sof evenC2_i0 evenC2_i1)
  unfold GammaSF
  have h1 : Sof (F := evenC2) (n := 1) evenC2_i0 evenC2_i0 = 0 := by
    have h := Sof_antisymm (F := evenC2) (n := 1) evenC2_i0 evenC2_i0
    have h2 : (2 : ℚ) • Sof (F := evenC2) (n := 1) evenC2_i0 evenC2_i0 = 0 := by
      rw [two_smul]; nth_rewrite 2 [h]; abel
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  have h2 : Sof (F := evenC2) (n := 1) evenC2_i1 evenC2_i0 = -Sof evenC2_i0 evenC2_i1 :=
    Sof_antisymm (F := evenC2) (n := 1) evenC2_i1 evenC2_i0
  rw [h1, h2, smul_zero, zero_sub]
  simp only [smul_neg, neg_neg]

/-- **The `FF` kind, at `evenIdx 1`, `n = 1`.** External value:
`Γ(F_{0,1}, F_{1,2}) = -½β_{0,2}·F_{1,1} - ½β_{1,1}·F_{0,2}`.
Reduces by `rfl` directly — no antisymmetry bookkeeping needed for the `F`-kind. -/
theorem evenC2_GammaBasis_FF :
    GammaBasis (F := evenC2) (n := 1) (Fof evenC2_u0 evenC2_i0) (Fof evenC2_u1 evenC2_i1)
      = -(1 / 2 : ℚ) • (beta evenC2 1 evenC2_u0 evenC2_i1 • eN (Fof evenC2_u1 evenC2_i0)
          + beta evenC2 1 evenC2_u1 evenC2_i0 • eN (Fof evenC2_u0 evenC2_i1)) := rfl

/-- **The `LS` kind, at `evenIdx 1`, `n = 1`.** External value:
`Γ(L_{0,1}, S_{1,2}) = β_{0,1}F_{1,2} - β_{0,2}F_{1,1} + β_{1,1}F_{0,2} -
β_{1,2}F_{0,1}`. Reduces by `rfl` directly. -/
theorem evenC2_GammaBasis_LS :
    GammaBasis (F := evenC2) (n := 1) (Lof evenC2_u0 evenC2_u1)
        (Sum.inr (Sum.inl ⟨(evenC2_i0, evenC2_i1), by decide⟩))
      = beta evenC2 1 evenC2_u0 evenC2_i0 • eN (Fof evenC2_u1 evenC2_i1)
        - beta evenC2 1 evenC2_u0 evenC2_i1 • eN (Fof evenC2_u1 evenC2_i0)
        + beta evenC2 1 evenC2_u1 evenC2_i0 • eN (Fof evenC2_u0 evenC2_i1)
        - beta evenC2 1 evenC2_u1 evenC2_i1 • eN (Fof evenC2_u0 evenC2_i0) := rfl

end OspN
end OspOddDeformations
