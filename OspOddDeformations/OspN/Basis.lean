import OspOddDeformations.OspN.Index

/-!
# The lift basis, for every `osp(N|2n)`

The basis of `𝔤` and its coordinate module, with `S_{ij}` and `eN`, for an arbitrary
`FermionIndex F` (an earlier development for odd `N` fixed the fermion index). The boson side
(`Bmn.I`, `Bmn.J`, `Bmn.IKey`) is reused directly by import — nothing about it is
odd-`N`-specific; only the fermion side is general.
-/

namespace OspOddDeformations
namespace OspN

open Bmn (I J IKey)

/-- `P = ℚ[β_{u,i}]`, one generator per `(I n × F.K)` pair. -/
noncomputable abbrev Pmn (F : FermionIndex) (n : ℕ) : Type := MvPolynomial (I n × F.K) ℚ

noncomputable def beta (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) : Pmn F n :=
  MvPolynomial.X (u, i)

/-- The lift basis for a general `FermionIndex`: sorted boson pairs (`L`, by `IKey`,
as for odd `N`), sorted fermion pairs (`S`, by `F.key`), all boson-fermion pairs
(`F`). -/
def OspBasis (F : FermionIndex) (n : ℕ) : Type :=
  {p : I n × I n // IKey p.1 ≤ IKey p.2} ⊕ {p : F.K × F.K // F.key p.1 < F.key p.2}
    ⊕ (I n × F.K)

noncomputable instance (F : FermionIndex) (n : ℕ) : DecidableEq (OspBasis F n) :=
  Classical.decEq _
instance (F : FermionIndex) (n : ℕ) : Fintype (OspBasis F n) := by
  unfold OspBasis; infer_instance

def parity {F : FermionIndex} {n : ℕ} : OspBasis F n → ZMod 2
  | .inl _ => 0
  | .inr (.inl _) => 0
  | .inr (.inr _) => 1

def Lof {F : FermionIndex} {n : ℕ} (u v : I n) : OspBasis F n :=
  if h : IKey u ≤ IKey v then Sum.inl ⟨(u, v), h⟩
  else Sum.inl ⟨(v, u), (Nat.not_le.mp h).le⟩

def Fof {F : FermionIndex} {n : ℕ} (u : I n) (i : F.K) : OspBasis F n := Sum.inr (Sum.inr (u, i))

noncomputable abbrev OspMod (F : FermionIndex) (n : ℕ) : Type := OspBasis F n → Pmn F n

@[simp] lemma ospMod_zero_apply {F : FermionIndex} {n : ℕ} (k : OspBasis F n) :
    (0 : OspMod F n) k = 0 := rfl
@[simp] lemma ospMod_add_apply {F : FermionIndex} {n : ℕ} (x y : OspMod F n) (k : OspBasis F n) :
    (x + y) k = x k + y k := rfl
@[simp] lemma ospMod_smul_apply {F : FermionIndex} {n : ℕ} (c : Pmn F n) (x : OspMod F n)
    (k : OspBasis F n) : (c • x) k = c * x k := rfl
@[simp] lemma ospMod_neg_apply {F : FermionIndex} {n : ℕ} (x : OspMod F n) (k : OspBasis F n) :
    (-x) k = -x k := rfl

noncomputable def eN {F : FermionIndex} {n : ℕ} (b : OspBasis F n) : OspMod F n :=
  fun k => if k = b then 1 else 0

/-- `S_{ij}`, signed (`S_{ji} = -S_{ij}`, `S_{ii} = 0`): sorts by `F.key`, carrying the
sign directly. -/
noncomputable def Sof {F : FermionIndex} {n : ℕ} (i j : F.K) : OspMod F n :=
  if h : F.key i < F.key j then eN (Sum.inr (Sum.inl ⟨(i, j), h⟩) : OspBasis F n)
  else if h2 : F.key j < F.key i then -eN (Sum.inr (Sum.inl ⟨(j, i), h2⟩) : OspBasis F n)
  else 0

end OspN
end OspOddDeformations
