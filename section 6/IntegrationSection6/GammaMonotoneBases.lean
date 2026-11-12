import IntegrationSection6.FiniteGammaObjects

/-! Monotonicity of the mathematical Gamma base at a fixed internal code
presentation that contains the larger real parameter base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

structure GammaBaseInclusion (B C : Base (M := M)) where
  real_subset : B.real ⊆ C.real
  gamma_subset : B.gamma ⊆ C.gamma

variable {B C : Base (M := M)} {S : Set M} {n : ℕ}

def GammaBaseInclusion.objectAt (H : GammaBaseInclusion B C) (hCS : C.real ⊆ S)
    (U : FiniteRV.GammaObjectAt B S n) : FiniteRV.GammaObjectAt C S n where
  object := U.object
  real_contains := hCS
  domain_graph := U.domain_graph.mono H.real_subset H.gamma_subset
  volume_graph := U.volume_graph.mono H.real_subset H.gamma_subset

def GammaBaseInclusion.admissibleAt (H : GammaBaseInclusion B C) (hCS : C.real ⊆ S)
    (U : FiniteRV.GammaObjectAt B S n) (i : Fin n) (hAd : GammaAdmissible U.toGamma.toGammaRVObject i) :
    GammaAdmissible (H.objectAt hCS U).toGamma.toGammaRVObject i := by
  refine ⟨hAd.nonzero,?_⟩
  intro u
  exact (hAd.algebraic u).mono (Set.union_subset_union H.real_subset (Set.Subset.refl _)) H.gamma_subset

end IntegrationInACVF.Section6
