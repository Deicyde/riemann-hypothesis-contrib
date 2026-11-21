import BuildAid.Leniency.Open
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharNormDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane -- for `export` of Formalism.L2.Host.HChar, Formalism.L2.Host.hcharSub (+1 more)
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_char_norm_descent : ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M] (a : ℕ) (χ : HChar (maximalRealSubfield K)), (∀ v : InfinitePlace (maximalRealSubfield K), χ.locInf v (-1) = (-1) ^ a) → ∃ χ' : HChar (maximalRealSubfield M), (∀ u : InfinitePlace (maximalRealSubfield M), χ'.locInf u (-1) = (-1) ^ a) ∧ ∀ x : Ideles M, (compNorm M χ').1 x = (compNorm K χ).1 (GroundTheory.Global.ideleNorm K M x) := by
  first | exact @GlobalTheory.RealNormChar.main | exact GlobalTheory.RealNormChar.main | (intros; apply GlobalTheory.RealNormChar.main <;> assumption)
