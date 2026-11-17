module

public import Integration7.NativeUnaryProducts
public import IntegrationSection6.GammaGlobalRestriction

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Native unary products and their two actual factor projections have
complete original-Gamma set and graph certificates. -/
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
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {m : ℕ}

theorem gamma_native_unary_product (A : DefSet (M := M) S 1 m) (B : DefSet (M := M) S 1 0)
    (hA : GammaSetDefinable P (carrier A)) (hB : GammaSetDefinable P (carrier B)) :
    GammaSetDefinable P (carrier (nativeUnaryProductDomain A B)) := by
  let L := coordinateProjectMap 0 (PresentedSet.univ (pointSpace (M := M) 2 m) P.real)
  let R := mixedCoordinatePointMap (fun _ : Fin 1 => (1 : Fin 2)) (Fin.elim0 : Fin 0 → Fin m) P.real
  have h := (gammaLogicInput P).inter ((gammaLogicInput P).preimage_real L hA)
    ((gammaLogicInput P).preimage_real R hB)
  convert h using 1
  ext p
  have hR : (R ⟨p,Set.mem_univ _⟩).val = (show Point (M := M) 1 0 from
      ((fun _ : Fin 1 => vfAt p 1),Fin.elim0)) := Prod.ext rfl (Subsingleton.elim _ _)
  constructor
  · intro hp
    have hp' := (native_unary_product_carrier A B p).mp hp
    exact ⟨⟨⟨p,Set.mem_univ _⟩,rfl,hp'.1⟩,
      ⟨⟨p,Set.mem_univ _⟩,rfl,(congrArg (fun z : Point (M := M) 1 0 => z ∈ carrier B) hR).mpr hp'.2⟩⟩
  · rintro ⟨⟨a,ha,hpa⟩,⟨b,hb,hpb⟩⟩
    have ha' : a = ⟨p,Set.mem_univ _⟩ := Subtype.ext ha
    have hb' : b = ⟨p,Set.mem_univ _⟩ := Subtype.ext hb
    rw [ha'] at hpa
    rw [hb'] at hpb
    exact (native_unary_product_carrier A B p).mpr
      ⟨hpa,(congrArg (fun z : Point (M := M) 1 0 => z ∈ carrier B) hR).mp hpb⟩

theorem gamma_native_unary_product_left (A : DefSet (M := M) S 1 m) (B : DefSet (M := M) S 1 0)
    (hA : GammaSetDefinable P (carrier A)) (hB : GammaSetDefinable P (carrier B)) :
    GammaGraphDefinable P (pointMapGraph (nativeUnaryProductLeftMap A B)) :=
  gamma_map_graph_of_global_formula _
    (coordinateProjectMap 0 (PresentedSet.univ (pointSpace (M := M) 2 m) P.real))
    (gamma_native_unary_product A B hA hB) (fun _ => rfl)

theorem gamma_native_unary_product_right (A : DefSet (M := M) S 1 m) (B : DefSet (M := M) S 1 0)
    (hA : GammaSetDefinable P (carrier A)) (hB : GammaSetDefinable P (carrier B)) :
    GammaGraphDefinable P (pointMapGraph (nativeUnaryProductRightMap A B)) :=
  gamma_map_graph_of_global_formula _
    (mixedCoordinatePointMap (fun _ : Fin 1 => (1 : Fin 2)) (Fin.elim0 : Fin 0 → Fin m) P.real)
    (gamma_native_unary_product A B hA hB) (fun _ => rfl)

end IntegrationInACVF.Section7
