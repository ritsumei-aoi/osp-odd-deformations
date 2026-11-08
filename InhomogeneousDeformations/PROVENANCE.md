# Provenance of the copied modules

Copied from `https://github.com/ritsumei-aoi/osp-triviality`, tag `v2.2-lean4.34`
(commit `bd82df81fb34ca5f1688dc113968ef03ae630f75`), directory `InhomogeneousDeformations/`, under its MIT licence
(same copyright holder; see `LICENSE`). These are the modules this development imports from that repository, with
their own imports. They were copied unchanged; the port to Lean `v4.35.0` changed two of them, as listed
below. sha256 of each file as copied:

| file | sha256 |
|---|---|
| `Indexed.lean` | `050c14ce24f225705fc6984e7e0696112de22c30764aaec1d6337b6334c1d733` |
| `IndexedCoboundary.lean` | `bb220fa087054e5576f20f0d5df71de848b2b8ec355de69cdfc364dbeaea7b10` |
| `IndexedJacobi.lean` | `b70c22ed4c9c77ddeee59903e1cdca1fe53a4266aa3d2c24d0606d0212a03e89` |
| `IndexedKappa.lean` | `7a7ebc8dc93e3ddf60581bfd5e97d6d85afbdf32a529d7a22e40e56d0dbb5dbd` |
| `IndexedLaws.lean` | `29d0dc7f69f9ab31e009a20bfc4daeb12ee04dc369da276d2d8936ab295a1461` |
| `IndexedU.lean` | `9776f0e98984d0eb939573bf0d3df1fa977181483958bf34a0d6220911c2a8ec` |
| `SourceC.lean` | `f19b027d7b16c58cda5a77d78e48336977d78f23626a282b8c28f65201af33a1` |
| `SourceIndependence.lean` | `4caf76161eb17e067997d5d68bdee96ec531f113532e8b312e9702275a51030e` |
| `SourceLifts.lean` | `6a5b1cfea3cd0cc4e5fe537f5736cbdb2086e60d6ffb2a3ab81e5fda78ea46ab` |
| `SourceQuadraticIndependence.lean` | `b92c17e1af4d3edaaf764c0e54764782477ce32eb47c3c8925f53bc801c13c3e` |
| `SourceTensor.lean` | `608d0cf8c88733f050c7ef05759b245a3cd4b1da2f6db1e5f137cf6d6edee5ab` |
| `SourceWeyl.lean` | `6d8b0b845b11e62dee2f03ff928b240e2c4123a8795e9dc650f2f5f608f733d1` |

## Changes in the port to Lean v4.35.0 (mathlib `v4.35.0`)

No statement and no proof text changed (each declaration compared with the source commit above).
- `Indexed.lean`: the import `Mathlib.Data.Prod.Lex`, deprecated, replaced by `Mathlib.Order.Prod.Lex.Basic` as
  the deprecation notice directs. sha256 now `a266c98a9effbf841ac819e296079f835d56720a48cc619e2d07612674926942`.
- `IndexedLaws.lean`: a comment line and `set_option linter.unusedTactic false in` before `Jn_antisymm`, whose `first` lists an
  alternative that this toolchain reports unused. sha256 now `14a5bf2f961c24a716cd37999a14c7f1fb6fe2f7a6a1f396b7fd64b5c1b7be8a`.
