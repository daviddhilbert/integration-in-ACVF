module

public import Integration7.NativeVFProjectionDomains
public import Integration7.BalancedCellTranslationEquivalences

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The positioning function of a balanced cell is an actual definable
bijection between its two native unary projection domains. Its complete
graph stays over the original Gamma base. -/
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
open IntegrationInACVF.Section5 IntegrationInACVF.Section4
open IntegrationInACVF.Section4.Cells IntegrationInACVF.Section4.BalancedFibres

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {ε : VF (M := M) → VF (M := M)} {r t : RV (M := M)}

def balancedNativePositionMap (A : DefSet (M := M) S 2 0)
    (h : HasBalancedFibres (first (nativeVFPairDomain A)) (second (nativeVFPairDomain A))
      (nativeVFPairDomain A) ε r t)
    (hf : DefinableOver S (fun _ : Fin 2 => .vf) (positionCodes (first (nativeVFPairDomain A)) ε)) :
    Map (nativeVFProjectionDomain A 0) (nativeVFProjectionDomain A 1) :=
  let U := nativeVFProjectionDomain A 0
  let hD : ∀ p : U, vfAt p.val 0 ∈ first (nativeVFPairDomain A) := fun p =>
    (native_vf_first_projection A p.val).mp p.property
  let c := coordinatePositionCentreMap U 0 (first (nativeVFPairDomain A)) ε hf hD
  mapIntoSubset (nativeScalarPointMap c) (nativeVFProjectionDomain A 1) (fun p =>
    (native_vf_second_projection A (nativeScalarPointMap c p).val).mpr (h.bijective.mapsTo (hD p)))

theorem balanced_native_position_value (A : DefSet (M := M) S 2 0)
    (h : HasBalancedFibres (first (nativeVFPairDomain A)) (second (nativeVFPairDomain A))
      (nativeVFPairDomain A) ε r t)
    (hf : DefinableOver S (fun _ : Fin 2 => .vf) (positionCodes (first (nativeVFPairDomain A)) ε))
    (p : nativeVFProjectionDomain A 0) :
    vfAt (balancedNativePositionMap A h hf p).val 0 = ε (vfAt p.val 0) := rfl

theorem balanced_native_position_bijective (A : DefSet (M := M) S 2 0)
    (h : HasBalancedFibres (first (nativeVFPairDomain A)) (second (nativeVFPairDomain A))
      (nativeVFPairDomain A) ε r t)
    (hf : DefinableOver S (fun _ : Fin 2 => .vf) (positionCodes (first (nativeVFPairDomain A)) ε)) :
    Function.Bijective (balancedNativePositionMap A h hf) := by
  constructor
  · intro p q he
    have hv := congrArg (fun z => vfAt z.val 0) he
    rw [balanced_native_position_value,balanced_native_position_value] at hv
    have hp := (native_vf_first_projection A p.val).mp p.property
    have hq := (native_vf_first_projection A q.val).mp q.property
    have he0 := h.bijective.injOn hp hq hv
    apply Subtype.ext
    refine Prod.ext ?_ (Subsingleton.elim _ _)
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact he0
  · intro q
    have hq := (native_vf_second_projection A q.val).mp q.property
    obtain ⟨x,hx,he⟩ := h.bijective.surjOn hq
    let p : Point (M := M) 1 0 := (fun _ => x,Fin.elim0)
    let u : nativeVFProjectionDomain A 0 := ⟨p,(native_vf_first_projection A p).mpr hx⟩
    refine ⟨u,Subtype.ext (Prod.ext ?_ (Subsingleton.elim _ _))⟩
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact he

theorem gamma_balanced_native_position_map {B : Base (M := M)}
    (A : DefSet (M := M) S 2 0) (hA : GammaSetDefinable B (carrier A))
    (h : HasBalancedFibres (first (nativeVFPairDomain A)) (second (nativeVFPairDomain A))
      (nativeVFPairDomain A) ε r t)
    (hf : DefinableOver S (fun _ : Fin 2 => .vf) (positionCodes (first (nativeVFPairDomain A)) ε))
    (hfΓ : DefinableOverBase B (fun _ : Fin 2 => .vf) (positionCodes (first (nativeVFPairDomain A)) ε)) :
    GammaGraphDefinable B (pointMapGraph (balancedNativePositionMap A h hf)) := by
  let U := nativeVFProjectionDomain A 0
  let hD : ∀ p : U, vfAt p.val 0 ∈ first (nativeVFPairDomain A) := fun p =>
    (native_vf_first_projection A p.val).mp p.property
  let c := coordinatePositionCentreMap U 0 (first (nativeVFPairDomain A)) ε hf hD
  exact gamma_native_scalar_point_map c (coordinate_position_native_gamma_graph U
    (gamma_native_vf_projection_domain A 0 hA) 0 (first (nativeVFPairDomain A)) ε hf hfΓ hD)

end IntegrationInACVF.Section7
