module

public import Integration7.GammaNativeUnaryProducts
public import Integration7.NativeUnaryProductMaps
public import IntegrationSection5.GammaGraphOperations
public import Section5.GammaLiftRelation

@[expose] public section

/-! The action on a rectangular factor retains its complete graph over
Gamma, even when neither factor nor its special map is real-definable
at the original base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {m r : ℕ}
variable {A : DefSet (M := M) S 1 m} {D : DefSet (M := M) S 1 r}

theorem gamma_native_unary_product_map (f : Map A D) (B : DefSet (M := M) S 1 0)
    (hA : GammaSetDefinable P (carrier A)) (hB : GammaSetDefinable P (carrier B))
    (hf : GammaGraphDefinable P (pointMapGraph f)) :
    GammaGraphDefinable P (pointMapGraph (nativeUnaryProductMap f B)) := by
  let I := Map.id (PresentedSet.univ (pointSpace (M := M) 2 m) P.real)
  let L := coordinateProjectMap 0 (PresentedSet.univ (pointSpace (M := M) 2 r) P.real)
  let R := mixedCoordinatePointMap (fun _ : Fin 1 => (1 : Fin 2)) (Fin.elim0 : Fin 0 → Fin r) P.real
  have hLeft := gamma_composition_graph (nativeUnaryProductLeftMap A B) f
    (gamma_native_unary_product_left A B hA hB) hf
  have hRight := gamma_native_unary_product_right A B hA hB
  apply GammaGraphDefinable.congr (gammaGraph_inter (hLeft.preimage_maps I L) (hRight.preimage_maps I R))
  intro p q
  constructor
  · rintro ⟨⟨a,ha,hl⟩,⟨b,hb,hr⟩⟩
    have hba : b = a := Subtype.ext (hb.trans ha.symm)
    subst b
    refine ⟨a,ha,?_⟩
    rw [native_unary_product_map_value]
    have h0 := congrFun (congrArg Prod.fst hl) 0
    have h1 := congrFun (congrArg Prod.fst hr) 0
    have hv : (![ (f (nativeUnaryProductLeftMap A B a)).val.1 0,vfAt a.val 1] : Fin 2 → VF (M := M)) = q.1 := by
      funext i
      fin_cases i
      · exact h0
      · exact h1
    have hrv := congrArg Prod.snd hl
    exact Prod.ext hv hrv
  · rintro ⟨a,rfl,hq⟩
    refine ⟨⟨a,rfl,?_⟩,⟨a,rfl,?_⟩⟩
    · have h := congrArg (coordinateProject 0) hq
      have h' := congrArg Subtype.val (native_unary_product_map_left f B a)
      exact h'.symm.trans h
    · have h := congrArg (fun z : Point (M := M) 2 r => vfAt z 1) hq
      exact Prod.ext (funext (fun _ => h)) (Subsingleton.elim _ _)

end IntegrationInACVF.Section7
