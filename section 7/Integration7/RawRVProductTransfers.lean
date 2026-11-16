module

public import IntegrationSection5.StandardContractionLift
public import Section4.RVProduct
public import Section4.ProductBijections

@[expose] public section

/-! A native pure-RV bijection to a Cartesian product transfers to the
actual packed raw RV domains, preserving the literal label tuples. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {a b c : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem raw_label_image_map_bijective (A : DefSet (M := M) S 0 a) :
    Function.Bijective (Map.toImage (rawLabelMap A)) := by
  constructor
  · intro p q he
    have hr := congrArg Subtype.val he
    exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) hr)
  · rintro ⟨q,p,hp⟩
    exact ⟨p,Subtype.ext hp⟩

def rawLabelImageInverse (A : DefSet (M := M) S 0 a) :=
  Map.inverse (Map.toImage (rawLabelMap A)) (raw_label_image_map_bijective A)

theorem raw_label_image_inverse_bijective (A : DefSet (M := M) S 0 a) :
    Function.Bijective (rawLabelImageInverse A) := by
  constructor
  · intro p q he
    have h := congrArg (Map.toImage (rawLabelMap A)) he
    exact (Map.apply_inverse _ _ p).symm.trans (h.trans (Map.apply_inverse _ _ q))
  · intro p
    exact ⟨Map.toImage (rawLabelMap A) p,Map.inverse_apply _ _ p⟩

def rawRVProductTransfer {A : DefSet (M := M) S 0 a} {B : DefSet (M := M) S 0 b}
    {C : DefSet (M := M) S 0 c} (f : Map A (PresentedSet.prod B C)) :=
  Map.comp (Map.toImage (@SpecialTransformations.Section4.rvPack M N S b c
    (Map.image (rawLabelMap B)) (Map.image (rawLabelMap C))))
    (Map.comp (@SpecialTransformations.DefinableGeometry.Map.prodMap LRV M N _ _ _ _ S _ _ _ _
      (Map.toImage (rawLabelMap B)) (Map.toImage (rawLabelMap C)))
      (Map.comp f (rawLabelImageInverse A)))

theorem raw_rv_product_transfer_bijective {A : DefSet (M := M) S 0 a}
    {B : DefSet (M := M) S 0 b} {C : DefSet (M := M) S 0 c}
    (f : Map A (PresentedSet.prod B C)) (hf : Function.Bijective f) :
    Function.Bijective (rawRVProductTransfer f) :=
  (@SpecialTransformations.Section4.rvPackToImage_bijective M N S b c _ _).comp
    ((@SpecialTransformations.DefinableGeometry.Map.prodMap_bijective LRV M N _ _ _ _ S _ _ _ _ _ _
      (raw_label_image_map_bijective B) (raw_label_image_map_bijective C)).comp
      (hf.comp (raw_label_image_inverse_bijective A)))

theorem raw_rv_product_transfer_value {A : DefSet (M := M) S 0 a}
    {B : DefSet (M := M) S 0 b} {C : DefSet (M := M) S 0 c}
    (f : Map A (PresentedSet.prod B C)) (p : A) :
    (rawRVProductTransfer f (Map.toImage (rawLabelMap A) p)).val =
      Fin.append (f p).val.1.2 (f p).val.2.2 := by
  change Fin.append (f (rawLabelImageInverse A (Map.toImage (rawLabelMap A) p))).val.1.2
    (f (rawLabelImageInverse A (Map.toImage (rawLabelMap A) p))).val.2.2 = _
  rw [rawLabelImageInverse,Map.inverse_apply]

end IntegrationInACVF.Section7
