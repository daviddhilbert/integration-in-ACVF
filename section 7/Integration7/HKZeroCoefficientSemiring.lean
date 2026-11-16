import Integration7.HKVolumeBlowupSemiring
import Section4.RVProductSymmetry

/-! The actual weighted degree-zero coefficient semiring is commutative:
swapping the two finite factors exchanges, and therefore preserves, their
multiplied RV forms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def zeroProductSwapIso (Z T : ZeroRVVolumeObject (M := M) S) :
    ZeroRVVolumeIso (product S 0 0 Z T) (product S 0 0 T Z) := by
  apply ZeroRVVolumeIso.ofBijection (rvProductSwapMap Z.underlying.obj T.underlying.obj)
    (rvProductSwapMap_bijective Z.underlying.obj T.underlying.obj)
  intro a
  obtain ⟨z,t,rfl⟩ := exists_rvPackPair Z.underlying.obj.domain T.underlying.obj.domain a
  rw [rvProductSwapMap_pair]
  exact (product_density_pair 0 0 Z T z t).trans
    ((mul_comm _ _).trans (product_density_pair 0 0 T Z t z).symm)

instance zeroCoefficientCommSemiring
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    CommSemiring (RVBlowupClasses hc C 0) where
  toSemiring := inferInstance
  mul_comm z t := Quotient.inductionOn₂ z t (fun Z T => Quotient.sound ⟨zeroProductSwapIso Z T⟩)

end IntegrationInACVF.Section7.HK
