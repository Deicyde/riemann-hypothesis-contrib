module

public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.SignDefiniteness.ExplicitFunctionSquareIntegrable
import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.ExplicitFunctionSquareIntegrable

@[expose] public section

namespace CompanionTheory.RgFd

open CompanionTheory.RgDs

theorem psiNorm : PsiNorm := PositivityTheory.RgFd.psiNorm

theorem explicit_function_square_integrable : ExplicitFunctionSquareIntegrable := square_integrable_of_norm psiNorm

end CompanionTheory.RgFd
