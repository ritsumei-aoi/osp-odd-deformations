import OspOddDeformations.OspN.Basis

/-!
# `bracket0Basis`, for every `osp(N|2n)`

The base bracket `[·,·]_0` of paper Lemma 3.2 (eqs. (3.1)–(3.6)) on basis elements, written with
`F.dual`/`F.g` for a general `FermionIndex`. None of the six rules mentions the concrete shape
of the fermion index.
-/

namespace OspOddDeformations
namespace OspN

open Bmn (I J)

noncomputable def bracketLL {F : FermionIndex} {n : ℕ} (u v w z : I n) : OspMod F n :=
  (1 / 2 * J n v w) • eN (Lof u z) + (1 / 2 * J n u w) • eN (Lof v z)
  + (1 / 2 * J n v z) • eN (Lof u w) + (1 / 2 * J n u z) • eN (Lof v w)

noncomputable def bracketSS {F : FermionIndex} {n : ℕ} (i j k l : F.K) : OspMod F n :=
  (F.g j k) • Sof i l - (F.g i k) • Sof j l - (F.g j l) • Sof i k + (F.g i l) • Sof j k

noncomputable def bracketLF {F : FermionIndex} {n : ℕ} (u v w : I n) (i : F.K) : OspMod F n :=
  (1 / 2 * J n v w) • eN (Fof u i) + (1 / 2 * J n u w) • eN (Fof v i)

noncomputable def bracketSF {F : FermionIndex} {n : ℕ} (j k : F.K) (w : I n) (i : F.K) :
    OspMod F n :=
  (F.g k i) • eN (Fof w j) - (F.g j i) • eN (Fof w k)

noncomputable def bracketFF {F : FermionIndex} {n : ℕ} (u : I n) (i : F.K) (v : I n) (j : F.K) :
    OspMod F n :=
  (1 / 4 * J n u v) • Sof i j + (1 / 2 * F.g i j) • eN (Lof u v)

noncomputable def bracket0Basis {F : FermionIndex} {n : ℕ} :
    OspBasis F n → OspBasis F n → OspMod F n
  | .inl ⟨(u, v), _⟩, .inl ⟨(w, z), _⟩ => bracketLL u v w z
  | .inl _, .inr (.inl _) => 0
  | .inl ⟨(u, v), _⟩, .inr (.inr (w, i)) => bracketLF u v w i
  | .inr (.inl _), .inl _ => 0
  | .inr (.inl ⟨(i, j), _⟩), .inr (.inl ⟨(k, l), _⟩) => bracketSS i j k l
  | .inr (.inl ⟨(j, k), _⟩), .inr (.inr (w, i)) => bracketSF j k w i
  | .inr (.inr (w, i)), .inl ⟨(u, v), _⟩ => -bracketLF u v w i
  | .inr (.inr (w, i)), .inr (.inl ⟨(j, k), _⟩) => -bracketSF j k w i
  | .inr (.inr (u, i)), .inr (.inr (v, j)) => bracketFF u i v j

noncomputable def bracket0 {F : FermionIndex} {n : ℕ} (x y : OspMod F n) : OspMod F n :=
  ∑ i : OspBasis F n, ∑ j : OspBasis F n, (x i * y j) • bracket0Basis i j

noncomputable def gsign (p q : ZMod 2) : ℚ := if p = 1 ∧ q = 1 then -1 else 1

end OspN
end OspOddDeformations
