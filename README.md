# Black hole research

Research papers and their Lean formalizations by Naoki Takata. Each study has its own directory under `papers/`. The papers share a pinned Lean environment.

## Papers

| Paper | Published on GitHub | Files |
| --- | --- | --- |
| The mass–volume–area hierarchy for Kerr black holes in *f(R)* gravity | 25 November 2026 | [Paper (PDF)](output/pdf/kerr-volume-hierarchy.pdf) · [LaTeX and figure](papers/kerr-volume-hierarchy/) · [BibTeX](papers/kerr-volume-hierarchy/citation.bib) · [Version 1](https://github.com/nktkt/blackhole/tree/kerr-volume-hierarchy-v1) |

The paper gives an exact coupling interval for each uncharged, subextremal Kerr black hole on the Einstein branch of normalized *f(R)* gravity. The hierarchy holds throughout the family, including Schwarzschild, exactly when *f″(0) = 0*. The paper also derives the flat thermodynamic volume shift in arbitrary integer spacetime dimension *D ≥ 4* under the vacuum Smarr hypothesis. [Kerr proof](BlackHole/KerrScalarCurvature.lean) · [Volume shift](BlackHole/ScalarCurvatureGravity.lean)

**日本語**　真空アインシュタイン解として続くKerrブラックホールについて、質量・熱力学的体積・地平面積の不等式が成立する条件をLeanで証明しました。各解で許される結合定数の範囲と、回転ゼロを含む全非極限Kerr解で成立する条件を示しています。論文の本文は英語で、日本語要旨を併記しています。

## Reproduce the formal results

With [Elan](https://lean-lang.org/install/) installed, run the following from a fresh checkout. The toolchain file selects Lean 4.29.1 and the Lake manifest pins mathlib and its dependencies.

```sh
git clone https://github.com/nktkt/blackhole.git
cd blackhole
awk '$1 == "import" && $2 ~ /^Mathlib[.]/ {print $2}' BlackHole/*.lean | sort -u | xargs lake exe cache get
lake build
```

The following commands replay the two main modules with the Lean kernel.

```sh
lake env leanchecker --verbose BlackHole.ScalarCurvatureGravity
lake env leanchecker --verbose BlackHole.KerrScalarCurvature
```

| Result | Declaration | Source |
| --- | --- | --- |
| Volume shift at fixed Wald entropy and angular momenta | `volume_shift` | [ScalarCurvatureGravity](BlackHole/ScalarCurvatureGravity.lean) |
| Coupling interval at one Kerr state | `kerr_iff` | [KerrScalarCurvature](BlackHole/KerrScalarCurvature.lean) |
| Condition for all subextremal Kerr states | `all_kerr_iff` | [KerrScalarCurvature](BlackHole/KerrScalarCurvature.lean) |
| Volume from the linearized constraints | `flat_volume_from_adjoint` | [PressureResponse](BlackHole/PressureResponse.lean) |
| Exact decision with program-specified couplings | `no_total_classifier` | [ComputableCouplings](BlackHole/ComputableCouplings.lean) |

## Rebuild the paper

A TeX Live installation with LuaLaTeX, LuaTeX-ja, Libertinus, Harano Aji and `latexmk` builds the English manuscript and Japanese abstract. From the repository root, run

```sh
mkdir -p .build/kerr-volume-hierarchy output/pdf
(
  cd papers/kerr-volume-hierarchy
  latexmk -lualatex -interaction=nonstopmode -halt-on-error \
    -outdir=../../.build/kerr-volume-hierarchy kerr-volume-hierarchy.tex
)
cp .build/kerr-volume-hierarchy/kerr-volume-hierarchy.pdf output/pdf/
```

The vector figure is included. To redraw it from the equations, run `python3 papers/kerr-volume-hierarchy/figures/coupling_interval.py` in an environment with ReportLab installed.
