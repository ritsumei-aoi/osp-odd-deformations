import OspOddDeformations.OspN.HTilde

/-!
# `GammaBasis` and `deltaBasis`, for every `osp(N|2n)`

Data only: the coefficient `Γ_β` of paper Proposition 4.4 on basis elements, and the coboundary
`δf` of eq. (4.1), for a general `FermionIndex`. The identity `Γ_β = δh̃`
(`Gamma_eq_delta_hTilde`) is proved in `OspN/Coboundary.lean`.
-/

namespace OspOddDeformations
namespace OspN

open Bmn (I)

noncomputable def GammaLS {F : FermionIndex} {n : ℕ} (u v : I n) (i j : F.K) : OspMod F n :=
  beta F n u i • eN (Fof v j) - beta F n u j • eN (Fof v i)
  + beta F n v i • eN (Fof u j) - beta F n v j • eN (Fof u i)

noncomputable def GammaLF {F : FermionIndex} {n : ℕ} (u v w : I n) (k : F.K) : OspMod F n :=
  (1 / 2 : ℚ) • (beta F n u k • eN (Lof v w) + beta F n v k • eN (Lof u w))

noncomputable def GammaSF {F : FermionIndex} {n : ℕ} (i j : F.K) (w : I n) (k : F.K) :
    OspMod F n :=
  (1 / 2 : ℚ) • (beta F n w j • Sof i k - beta F n w i • Sof j k)

noncomputable def GammaFF {F : FermionIndex} {n : ℕ} (u : I n) (i : F.K) (v : I n) (j : F.K) :
    OspMod F n :=
  -(1 / 2 : ℚ) • (beta F n u j • eN (Fof v i) + beta F n v i • eN (Fof u j))

noncomputable def GammaBasis {F : FermionIndex} {n : ℕ} : OspBasis F n → OspBasis F n → OspMod F n
  | .inl _, .inl _ => 0
  | .inl ⟨(u, v), _⟩, .inr (.inl ⟨(i, j), _⟩) => GammaLS u v i j
  | .inl ⟨(u, v), _⟩, .inr (.inr (w, k)) => GammaLF u v w k
  | .inr (.inl ⟨(i, j), _⟩), .inl ⟨(u, v), _⟩ => -GammaLS u v i j
  | .inr (.inl _), .inr (.inl _) => 0
  | .inr (.inl ⟨(i, j), _⟩), .inr (.inr (w, k)) => GammaSF i j w k
  | .inr (.inr (w, k)), .inl ⟨(u, v), _⟩ => -GammaLF u v w k
  | .inr (.inr (w, k)), .inr (.inl ⟨(i, j), _⟩) => -GammaSF i j w k
  | .inr (.inr (u, i)), .inr (.inr (v, j)) => GammaFF u i v j

noncomputable def Gamma {F : FermionIndex} {n : ℕ} (x y : OspMod F n) : OspMod F n :=
  ∑ i : OspBasis F n, ∑ j : OspBasis F n, (x i * y j) • GammaBasis i j

noncomputable def deltaBasis {F : FermionIndex} {n : ℕ} (f : OspMod F n → OspMod F n)
    (X Y : OspBasis F n) : OspMod F n :=
  bracket0 (f (eN X)) (eN Y) + gsign (parity X) 1 • bracket0 (eN X) (f (eN Y))
    - f (bracket0 (eN X) (eN Y))

noncomputable def delta {F : FermionIndex} {n : ℕ} (f : OspMod F n → OspMod F n)
    (x y : OspMod F n) : OspMod F n :=
  ∑ i : OspBasis F n, ∑ j : OspBasis F n, (x i * y j) • deltaBasis f i j

end OspN
end OspOddDeformations
