import OspOddDeformations.OspN.Laws

/-!
# `hTilde`, for every `osp(N|2n)`

The odd `P`-linear map `h̃` of paper Proposition 4.1, on basis elements and by linear extension,
for a general `FermionIndex`. Pure data, no proof content.
-/

namespace OspOddDeformations
namespace OspN

open Bmn (I)

noncomputable def hTildeBasis {F : FermionIndex} {n : ℕ} : OspBasis F n → OspMod F n
  | .inl ⟨(u, v), _⟩ =>
      ∑ i : F.K, (beta F n u (F.dual i) • eN (Fof v i) + beta F n v (F.dual i) • eN (Fof u i))
  | .inr (.inl _) => 0
  | .inr (.inr (u, i)) =>
      (1 / 2 : ℚ) • ∑ j : F.K, beta F n u j • Sof (F.dual j) i

noncomputable def hTilde {F : FermionIndex} {n : ℕ} (x : OspMod F n) : OspMod F n :=
  ∑ i : OspBasis F n, x i • hTildeBasis i

end OspN
end OspOddDeformations
