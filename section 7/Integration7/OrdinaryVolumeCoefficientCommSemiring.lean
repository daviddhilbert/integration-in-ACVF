module

public import Integration7.AllDegreeVolumeBlowupSemiring
public import Integration7.NondegenerateFiniteIso
public import Section4.RVProductSymmetry

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The ordinary degree-zero coefficient semiring is commutative,
by the actual swap of the two finite RV factors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

instance ordinaryRVVolumeCoefficientCommSemiring
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    CommSemiring (RVVolumeBlowupClasses hc C 0) where
  toSemiring := inferInstance
  mul_comm z t := Quotient.inductionOn₂ z t (fun Z T =>
    Quotient.sound ⟨finiteIsoOfNondegenerateBijection
      (rvProductSwapMap Z.obj T.obj) (rvProductSwapMap_bijective Z.obj T.obj)
      (fun _ i => i.elim0) (fun _ i => i.elim0)⟩)

end IntegrationInACVF.Section7
