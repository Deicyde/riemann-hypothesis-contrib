module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalDictionary
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_global_dictionary : PositivityTheory.RgEis.Dict := by
  exact @GlobalTheory.CompanionTheory.EisDict.dict
