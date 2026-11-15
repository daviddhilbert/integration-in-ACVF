import Integration7.NondegenerateFiniteIso
import Integration7.VFVolumeLifts

/-! Ordinary degree zero is retained: the lift-label projection is an
actual definable bijection, so lift isomorphisms are exactly RV[0]
isomorphisms. No positive-degree volume form is introduced. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

theorem zero_lift_label_map_bijective (U : RVObject (M := M) S 0) :
    Function.Bijective (liftLabelMap U) := by
  constructor
  · intro p q he
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact i.elim0
    · exact congrArg (fun u : U.domain => u.val) he
  · intro u
    refine ⟨⟨(Fin.elim0,u.val),u,rfl,?_⟩,rfl⟩
    funext i
    exact i.elim0

def ordinaryZeroLiftIsoOfRVIso {U V : RVFiniteObject (M := M) S 0} (e : U ≅ V) :
    rvLiftFiniteObject (rawRVSpace (M := M) 1) U ≅ rvLiftFiniteObject (rawRVSpace (M := M) 1) V := by
  let g := ((liftLabelMap V.obj).inverse (zero_lift_label_map_bijective V.obj)).comp
    ((finiteIsoMap e).comp (liftLabelMap U.obj))
  have hInv : Function.Bijective ((liftLabelMap V.obj).inverse (zero_lift_label_map_bijective V.obj)) :=
    (Equiv.ofBijective (liftLabelMap V.obj) (zero_lift_label_map_bijective V.obj)).symm.bijective
  apply ObjectProperty.isoMk
  apply ObjectProperty.isoMk
  exact DefinableSetCat.isoOfBijective g (hInv.comp ((finiteIsoMap_bijective e).comp (zero_lift_label_map_bijective U.obj)))

def ordinaryRVIsoOfZeroLiftIso {U V : RVFiniteObject (M := M) S 0}
    (e : rvLiftFiniteObject (rawRVSpace (M := M) 1) U ≅ rvLiftFiniteObject (rawRVSpace (M := M) 1) V) : U ≅ V := by
  let eRaw := (vfDimensionProperty (rawRVSpace (M := M) 1) S 0).ι.mapIso
    ((vfBoundedFiniteProperty (rawRVSpace (M := M) 1) S 0).ι.mapIso e)
  let f : Map (rvLift U.obj) (rvLift V.obj) := eRaw.hom
  have hf : Function.Bijective f := DefinableSetCat.bijective_of_iso eRaw
  let g := (liftLabelMap V.obj).comp (f.comp ((liftLabelMap U.obj).inverse (zero_lift_label_map_bijective U.obj)))
  have hInv : Function.Bijective ((liftLabelMap U.obj).inverse (zero_lift_label_map_bijective U.obj)) :=
    (Equiv.ofBijective (liftLabelMap U.obj) (zero_lift_label_map_bijective U.obj)).symm.bijective
  exact finiteIsoOfNondegenerateBijection g ((zero_lift_label_map_bijective V.obj).comp (hf.comp hInv))
    (fun _ i => i.elim0) (fun _ i => i.elim0)

theorem ordinary_zero_lift_iso_iff (U V : RVFiniteObject (M := M) S 0) :
    Nonempty (rvLiftFiniteObject (rawRVSpace (M := M) 1) U ≅ rvLiftFiniteObject (rawRVSpace (M := M) 1) V) ↔
      Nonempty (U ≅ V) :=
  ⟨fun ⟨e⟩ => ⟨ordinaryRVIsoOfZeroLiftIso e⟩,fun ⟨e⟩ => ⟨ordinaryZeroLiftIsoOfRVIso e⟩⟩

end IntegrationInACVF.Section7
