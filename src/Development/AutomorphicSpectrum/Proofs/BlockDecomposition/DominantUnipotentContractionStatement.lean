module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantUnipotentContraction
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_unipotent_contraction : PositivityTheory.SphericalProduct.DomU := by
  exact @GlobalTheory.CompanionTheory.DomUnitary.domU
