import Section4.RVProductAssociativity
import Section4.RVProductMorphisms

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] {S : Set M} {k l : ℕ}

theorem rvProductMap_pair_labels {U U' : RVObject (M := M) S k} {V V' : RVObject (M := M) S l}
    (F : Map U.domain U'.domain) (G : Map V.domain V'.domain) (u : U.domain) (v : V.domain) :
    (rvProductMap F G (rvPackPair U.domain V.domain u v)).val = Fin.append (F u).val (G v).val := by
  change ((rvPack U'.domain V'.domain).toImage
    (Map.prodMap F G (rvUnpack U.domain V.domain
      ((rvPack U.domain V.domain).toImage ⟨(u.val,v.val),u.property,v.property⟩)))).val = _
  rw [rvUnpack_pack,Map.prodMap_mk]
  rfl

end IntegrationInACVF.Section6
