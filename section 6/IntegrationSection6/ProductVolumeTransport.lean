import Section4.RVProductMorphisms

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] {S : Set M} {k l : ℕ}

theorem rvProductMap_volume_of_volume {U U' : RVObject (M := M) S k} {V V' : RVObject (M := M) S l}
    (F : Map U.domain U'.domain) (G : Map V.domain V'.domain)
    (hF : ∀ u, U'.value (F u) = U.value u) (hG : ∀ v, V'.value (G v) = V.value v)
    (x : (rvProductObject U V).domain) :
    (rvProductObject U' V').value (rvProductMap F G x) = (rvProductObject U V).value x := by
  rw [rvProductMap_value,rvProductObject_value,hF,hG]

end IntegrationInACVF.Section6
