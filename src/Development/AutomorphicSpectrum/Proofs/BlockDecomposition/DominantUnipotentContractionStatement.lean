module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantUnipotentContraction
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG PositivityTheory.SphericalProduct

theorem _root_.GlobalTheory.T.dominant_unipotent_contraction : PositivityTheory.SphericalProduct.DomU := by
  first | exact @GlobalTheory.CompanionTheory.DomUnitary.domU | exact GlobalTheory.CompanionTheory.DomUnitary.domU | (intros; apply GlobalTheory.CompanionTheory.DomUnitary.domU <;> assumption)
