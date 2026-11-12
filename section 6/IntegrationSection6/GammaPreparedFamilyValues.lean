import IntegrationSection6.GammaPreparedFamilyImages

/-! The prepared-family bijection changes the VF base and attaches its
key while preserving every original fibre RV label literally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p l a k : ℕ}
variable {A : Set (Point (M := M) p 0)} {C : Set (Point (M := M) p l)}

theorem gammaPreparedFamilyIso_value (e : GammaIso B A C) (hA : GammaSetDefinable B A)
    (F : GammaFiniteRVSchema B p a k) (z : vfSchemaSource A F) :
    ((gammaPreparedFamilyIso e hA F).equiv z).val =
      let c := e.equiv ⟨(z.val.1,Fin.elim0),z.property.1⟩
      (c.val.1,Fin.append (flatKey c.val).2 z.val.2) := by
  let v : pureVFExtension A a := ⟨z.val,vfSchemaSource_subset_extension F z.property⟩
  let b : A := ⟨(z.val.1,Fin.elim0),z.property.1⟩
  let c := e.equiv b
  let w := pureVFExtensionEquiv e.equiv a v
  have hBase : mixedRVBase w.val = c.val := pureVFExtensionEquiv_base e.equiv a v
  have hTail : mixedRVTail w.val = z.val.2 := pureVFExtensionEquiv_tail e.equiv a v
  change (preparedKeyExtensionMap B.real p l a ⟨w.val,Set.mem_univ _⟩).val = _
  rw [preparedKeyExtensionMap_value]
  have hVF := congrArg (fun u : Point (M := M) p l => u.1) hBase
  change (w.val.1,Fin.append (flatKey (mixedRVBase w.val)).2 (mixedRVTail w.val)) = _
  rw [hBase,hTail]
  exact congrArg (fun x => (x,Fin.append (flatKey c.val).2 z.val.2)) hVF

end IntegrationInACVF.Section6
