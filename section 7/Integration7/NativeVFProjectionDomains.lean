import Integration7.NativeVFPairImages
import IntegrationSection5.CoordinateFibreMaps
import IntegrationSection6.MixedCoordinatePointMaps
import IntegrationSection5.GammaGraphOperations
import Integration7.GammaPositionCodeCentres

/-! Actual unary VF projection domains of a native two-coordinate set,
with their precise pair projections and original-Gamma certificates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section4.Cells

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def nativeVFProjectionDomain (A : DefSet (M := M) S n 0) (j : Fin n) : DefSet (M := M) S 1 0 :=
  Map.image (coordinateProjectMap j A)

theorem mem_native_vf_projection_domain (A : DefSet (M := M) S n 0) (j : Fin n)
    (q : Point (M := M) 1 0) :
    q ∈ carrier (nativeVFProjectionDomain A j) ↔ ∃ p : A, vfAt p.val j = vfAt q 0 := by
  constructor
  · rintro ⟨p,he⟩
    exact ⟨p,congrArg (fun z => vfAt z 0) he⟩
  · rintro ⟨p,he⟩
    refine ⟨p,Prod.ext ?_ (Subsingleton.elim _ _)⟩
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact he

theorem native_vf_first_projection (A : DefSet (M := M) S 2 0) (q : Point (M := M) 1 0) :
    q ∈ carrier (nativeVFProjectionDomain A 0) ↔ vfAt q 0 ∈ first (nativeVFPairDomain A) := by
  rw [mem_native_vf_projection_domain]
  constructor
  · rintro ⟨p,he⟩
    exact ⟨twoVFPointPairEquiv p.val,⟨p.val,p.property,rfl⟩,he⟩
  · rintro ⟨z,⟨p,hp,he⟩,hz⟩
    exact ⟨⟨p,hp⟩,(congrArg Prod.fst he).trans hz⟩

theorem native_vf_second_projection (A : DefSet (M := M) S 2 0) (q : Point (M := M) 1 0) :
    q ∈ carrier (nativeVFProjectionDomain A 1) ↔ vfAt q 0 ∈ second (nativeVFPairDomain A) := by
  rw [mem_native_vf_projection_domain]
  constructor
  · rintro ⟨p,he⟩
    exact ⟨twoVFPointPairEquiv p.val,⟨p.val,p.property,rfl⟩,he⟩
  · rintro ⟨z,⟨p,hp,he⟩,hz⟩
    exact ⟨⟨p,hp⟩,(congrArg Prod.snd he).trans hz⟩

theorem gamma_native_vf_projection_domain {B : Base (M := M)}
    (A : DefSet (M := M) S n 0) (j : Fin n) (hA : GammaSetDefinable B (carrier A)) :
    GammaSetDefinable B (carrier (nativeVFProjectionDomain A j)) := by
  have h := (gammaLogicInput B).image_real
    (mixedCoordinatePointMap (fun _ : Fin 1 => j) (Fin.elim0 : Fin 0 → Fin 0) B.real) hA
  convert h using 1
  ext q
  constructor
  · rintro ⟨p,he⟩
    have hSame : (mixedCoordinatePointMap (fun _ : Fin 1 => j) (Fin.elim0 : Fin 0 → Fin 0)
        B.real ⟨p.val,Set.mem_univ _⟩).val = (coordinateProjectMap j A p).val :=
      Prod.ext rfl (Subsingleton.elim _ _)
    exact ⟨⟨p.val,Set.mem_univ _⟩,p.property,hSame.trans he⟩
  · rintro ⟨p,hp,he⟩
    have hSame : (coordinateProjectMap j A ⟨p.val,hp⟩).val =
        (mixedCoordinatePointMap (fun _ : Fin 1 => j) (Fin.elim0 : Fin 0 → Fin 0) B.real p).val :=
      Prod.ext rfl (Subsingleton.elim _ _)
    exact ⟨⟨p.val,hp⟩,hSame.trans he⟩

def nativeScalarPointMap {A : DefSet (M := M) S n 0}
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S)) :
    Map A (PresentedSet.univ (pointSpace 1 0) S) :=
  let empty := @SpecialTransformations.DefinableGeometry.Map.snd LRV M
    (CanonicalStructure.normalize (M := M)) (SpecialTransformations.Section4.vfSpace n)
    (SpecialTransformations.Section4.rvSpace 0) S A
  Map.comp (Map.inclusion (Set.subset_univ _)) (Map.pair c empty)

theorem native_scalar_point_value {A : DefSet (M := M) S n 0}
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S)) (p : A) :
    vfAt (nativeScalarPointMap c p).val 0 = (c p).val 0 := rfl

theorem gamma_native_scalar_point_map {B : Base (M := M)} {A : DefSet (M := M) S n 0}
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hΓ : GammaScalarGraphDefinable B (fun p z => ∃ q : A, q.val = p ∧ (c q).val 0 = z)) :
    GammaGraphDefinable B (pointMapGraph (nativeScalarPointMap c)) := by
  apply GammaGraphDefinable.congr hΓ
  intro p z
  constructor
  · rintro ⟨q,hq,hz⟩
    refine ⟨q,hq,Prod.ext ?_ (Subsingleton.elim _ _)⟩
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hz
  · rintro ⟨q,hq,hz⟩
    exact ⟨q,hq,congrArg (fun p => vfAt p 0) hz⟩

end IntegrationInACVF.Section7
