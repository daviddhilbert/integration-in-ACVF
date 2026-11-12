import IntegrationSection6.ContractionExtensionValues
import IntegrationSection6.OrderedSelectedVolume
import IntegrationSection6.GammaDegreeTransport

/-! Presentation extension preserves the recursively selected volume and
transports finite RV isomorphisms across equal natural degrees. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S R : Set M}

theorem extendContractionProgram_selectedIndex {n a l : ℕ}
    {U : DefSet (M := M) S n a} {V : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S U V) (hSR : S ⊆ R) {k : ℕ} (ρ : Fin k → Fin a) :
    orderedSelectedIndex (extendContractionProgram T hSR) ρ = orderedSelectedIndex T ρ := by
  induction T generalizing k with
  | zero U => rfl
  | step T tail ih => exact ih (headVolumeIndex T ρ)

def gammaRVIsoCastDegree {B : Base (M := M)} {k l : ℕ} (h : k = l)
    {U V : GammaRVFiniteObject B k} (e : GammaRVIso U.toGammaRVObject V.toGammaRVObject) :
    GammaRVIso (gammaCastDegree h U).toGammaRVObject (gammaCastDegree h V).toGammaRVObject := by
  cases h
  exact e

end IntegrationInACVF.Section6
