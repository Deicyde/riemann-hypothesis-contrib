# References to the literature

Which published results the statements of this formalization correspond to, recorded as
[Literature Links](https://github.com/mathlib-initiative/literature-links) annotations.

**These are a reader's proposals, not the author's account of the proof.** Each was proposed by one
AI session and judged independently by a second. No mathematician has checked them yet.
Corrections are welcome: open an issue or a pull request.

## What is here

[`references.jsonl`](references.jsonl) holds one annotation per line.

| Statement in the proof | Published result | Relation |
|---|---|---|
| `Deduction.landau_window` | E. Landau, *Über einen Satz von Tschebyschef*, Math. Ann. 61 (1905), Satz in §2, p. 536 | `relatedMatch` |
| `GlobalTheory.Published.BhattScholzeIntegral` | B. Bhatt and P. Scholze, *Prismatic F-crystals and crystalline Galois representations*, Camb. J. Math. 11 (2023), Theorem 5.6 | `narrowMatch` |
| `GlobalTheory.Published.BhattScholzeIntegral` | the same, Theorem 1.2 | `narrowMatch` |
| `UpperTheory.V.Z.Kato.WeilSphericalRecords.KatoTwoW` | K. Kato, *p-adic Hodge theory and values of zeta functions of modular forms*, Astérisque 295 (2004), Theorem 14.2 (1), p. 235 | `narrowMatch` |
| `UpperTheory.GalStar.Row0b` | A. Caraiani, *Monodromy and local-global compatibility for l = p*, Algebra Number Theory 8 (2014), Theorem 1.1 | `relatedMatch` |

## Reading an annotation

- **`subject`** is the published statement: an open copy of the source, the page of that PDF, a
  short quote that finds the statement, the citation and its identifiers.
- **`object`** is the Lean declaration and its module, at
  `40e56bab026552e089d7afcfeff08d2defb9c005`, the archive as published. The four files cited here
  are byte for byte the same on `main` at `2dea99006`.
- **`relation`** is read "source *relation* Lean":
  - `relatedMatch`: the source bears on the statement without stating it;
  - `narrowMatch`: the source's statement is more general, and the Lean is a case of it.
- **`note`** lists the differences between the two statements that a reader should know.
- **`extensions`** records how the link was reviewed.

## What gets in

1. The entry is mathematical content inside the proof, and the final theorem depends on it.
   Dependence does not show that the mathematics is essential to the argument: a statement can
   be passed along and never read. That needs the downstream proof traced.
2. The source was confirmed in a registry (Crossref, arXiv, zbMATH).
3. Two readers read the statement in the source, independently, and gave the same relation.
4. An independent account of the proof attributes the same source to the same statement. For
   these five that account is
   [the exposition for the Riemann zeta function](https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/zeta-paper.pdf)
   (draft of 21 November 2026), whose dependency runs are also the evidence for rule 1.

## Checking the file

```sh
python -m pip install "git+https://github.com/mathlib-initiative/literature-links@v1.0.2"
literature-links scan literature
```

This checks the format. It does not check the mathematics.
