# Inhomogeneous deformations of osp(N|2n): triviality for any number of odd parameters — the Lean formalization

This repository holds the Lean 4 formalization that accompanies the paper

> Hisashi Aoi, *Inhomogeneous deformations of osp(N|2n): triviality for any number of odd parameters*,
> arXiv:2611.11153 [math.RT], 2026. \[[arXiv](https://arxiv.org/abs/2611.11153)\]

The state that the paper describes is the tag `v1.0`.

The paper's Appendix A states what is formalized and what is not, and lists the declarations; this file
summarizes it. The formalization covers **every `N ≥ 1` and `n ≥ 1`**, and the statements of the
paper's Section 5 **every number `r ≥ 1`** of odd parameters. No declaration depends on `sorryAx`, and no
axiom is added.

## What is formalized

In the paper's numbering:

- the algebras `A_β` and `A_0`, presented by generators and relations, for one and for `r` odd
  parameters; the untwisting isomorphisms (Lemma 3.1, Theorem 5.1); the base bracket (Lemma 3.2);
  the independence of the lifts (Proposition 3.3); the identification with `osp(M, 𝓑)`
  (Proposition 3.4);
- the change of lifts (Propositions 4.1, 5.2), the recovery of the deformed bracket and the uniqueness
  of its coefficient (Theorems 4.2, 4.3, 5.3), and its values (Proposition 4.4);
- the triviality for one odd parameter (Theorem 4.5), the primitive `f_β` (Theorem 4.7,
  Corollary 4.8), every odd primitive (Theorem 4.9, Corollary 4.10), complex parameters
  (Corollary 4.11);
- the factorization of the trivialization (Proposition 5.4), the text after it, and its non-additivity
  (Proposition 5.5);
- the cases `N = 1` (controls against the formalization of that case, below), `C(2)` and `D(2,1)`.

Not formalized: the Fock module (Remark 5.7); the comparison with the oscillator realizations of
Frappat–Sciarrino–Sorba (Section 6); for `r ≤ 3`, that `Θ_* − id` has `κ`-degree 2 and square zero;
Remark 5.6; Remark 2.1; Remark 6.1 beyond the equivalence of `J − Ω` with `J` for `Ω` of `κ`-degree 2;
Remark 6.2 beyond `D(2,1)` itself (the Killing form of every `D(n+1,n)`, and which `D(2,1;α)` are
isomorphic to `D(2,1)`).

Two proofs differ from the paper's: Theorem 4.9 uses a grading element of `sp(2n)` instead of
Whitehead's lemma, and (5.3) follows from the identity `[UX, UY]_0 = U([X, Y]_0 + Σ_s κ_s Γ^{(s)}(X, Y))`
and Theorem 5.3.

## Building

Lean `v4.35.0`, mathlib `v4.35.0` (both pinned: `lean-toolchain`, `lake-manifest.json`).

```
lake exe cache get
lake build
```

The build includes `OspOddDeformations/OspN/Audit.lean`, which prints the axioms each listed
declaration depends on (`#print axioms`); every one depends on at most `propext`, `Classical.choice`
and `Quot.sound`.

## Layout

| directory | content |
|---|---|
| `OspOddDeformations/OspN/` | the development for every `N`: indices, the base bracket, the lifts, the coboundary, `f_β`, the identification |
| `OspOddDeformations/OspN/Presented/` | `A_β`, `A_0` presented by generators and relations; untwisting, recovery |
| `OspOddDeformations/OspN/Multi/` | several odd parameters: the Grassmann coefficients, `Θ`, `U`, the factorization |
| `OspOddDeformations/OspN/GroupB/` | Theorem 4.9, Corollaries 4.10–4.11, the normal form, the text after Proposition 5.4 (`Θ_*` is not `exp(ad Y)`), `D(2,1)` |
| `OspOddDeformations/General/` | general results, using mathlib only |
| `OspOddDeformations/Bmn/` | index types and forms |
| `InhomogeneousDeformations/` | twelve modules copied from the formalization of the case `N = 1` (below) |

## The blueprint

The blueprint is online at <https://ritsumei-aoi.github.io/osp-odd-deformations/>.
`blueprint/` is a separate Lake package ([VersoBlueprint](https://github.com/leanprover/verso-blueprint),
branch `v4.35.0`) that requires this development by path. Each node is a statement of the paper, with its
status (formalized, partially formalized, not formalized) and the declarations that formalize it, as listed
in `blueprint/NODE_MAP.md`. The chapters are generated from the paper's LaTeX source and the node map
(`gen_chapters.py --tex …`); `check_nodes.py` checks the built site against the node map.

```
cd blueprint
lake exe cache get
lake exe vbp build
python3 check_nodes.py
```

## The copied modules

`InhomogeneousDeformations/` holds twelve modules of
[`osp-triviality`](https://github.com/ritsumei-aoi/osp-triviality), the formalization that accompanies
H. Aoi, *On the triviality of inhomogeneous deformations of osp(1|2n)*, arXiv:2604.05252. They provide
the Weyl-algebra and graded-tensor-product infrastructure and the objects of the case `N = 1`, against
which the controls of this development are checked. They are copied from the tag `v2.2-lean4.34`, under
their own names, so that this repository builds by itself;
[`InhomogeneousDeformations/PROVENANCE.md`](InhomogeneousDeformations/PROVENANCE.md) gives the commit,
the sha256 of each file as copied, and the two changes made in the port to Lean `v4.35.0` (no statement
or proof changed).

## License

MIT; see [`LICENSE`](LICENSE). The copied modules are under the same license and copyright holder.
