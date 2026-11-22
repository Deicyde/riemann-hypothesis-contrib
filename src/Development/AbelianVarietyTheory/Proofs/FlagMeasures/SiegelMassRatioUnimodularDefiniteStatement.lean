module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMassRatioUnimodularDefinite
public import Formalism.HermitianLattices.StatementMass

@[expose] public section


theorem _root_.GlobalTheory.T.siegel_massRatio_unimodular_definite : Formalism.HermitianLatticesTheory.SiegelMassRatio := by
  first | exact @GlobalTheory.Mass.siegelMassRatio_holds | exact GlobalTheory.Mass.siegelMassRatio_holds | (intros; apply GlobalTheory.Mass.siegelMassRatio_holds <;> assumption)
