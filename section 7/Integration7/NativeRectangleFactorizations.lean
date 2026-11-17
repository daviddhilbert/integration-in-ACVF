module

public import Integration7.NativeUnaryProducts
public import Integration7.NativeVFPairImages
public import IntegrationSection6.GammaGlobalRestriction
public import IntegrationSection5.GammaPreparation

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! An actual native VF rectangle factors as the product of its two
actual unary projection images, retaining their original-Gamma domains. -/
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
variable {P : Base (M := M)} {S : Set M}

def nativeVFCoordinateDomain (A : DefSet (M := M) S 2 0) (i : Fin 2) : DefSet (M := M) S 1 0 :=
  Map.image (coordinateProjectMap i A)

theorem gamma_native_vf_coordinate_domain (A : DefSet (M := M) S 2 0) (i : Fin 2)
    (hA : GammaSetDefinable P (carrier A)) : GammaSetDefinable P (carrier (nativeVFCoordinateDomain A i)) := by
  have hMap := gamma_map_graph_of_global_formula (coordinateProjectMap i A)
    (coordinateProjectMap i (PresentedSet.univ (pointSpace (M := M) 2 0) P.real)) hA (fun _ => rfl)
  have h := (gammaLogicInput P).image_graph hMap
  convert h using 1
  ext q
  exact ⟨fun ⟨a,ha⟩ => ⟨a.val,a,rfl,ha⟩,fun ⟨_,a,_,ha⟩ => ⟨a,ha⟩⟩

theorem native_rectangle_projection_factorization (A : DefSet (M := M) S 2 0)
    (hMix : ∀ a b : A, (![vfAt a.val 0,vfAt b.val 1],Fin.elim0) ∈ carrier A) :
    A = nativeUnaryProductDomain (nativeVFCoordinateDomain A 0) (nativeVFCoordinateDomain A 1) := by
  apply PresentedSet.eq_of_carrier_eq
  ext p
  rw [native_unary_product_carrier]
  constructor
  · intro hp
    exact ⟨⟨⟨p,hp⟩,rfl⟩,⟨⟨p,hp⟩,Prod.ext rfl (Subsingleton.elim _ _)⟩⟩
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    have h0 := congrFun (congrArg Prod.fst ha) 0
    have h1 := congrFun (congrArg Prod.fst hb) 0
    have he : (show Point (M := M) 2 0 from (![vfAt a.val 0,vfAt b.val 1],Fin.elim0)) = p := by
      refine Prod.ext ?_ (Subsingleton.elim _ _)
      funext j
      fin_cases j
      · exact h0
      · exact h1
    exact (congrArg (fun q : Point (M := M) 2 0 => q ∈ carrier A) he).mp (hMix a b)

theorem native_rectangle_factorization_of_pair_product (A : DefSet (M := M) S 2 0)
    (X Y : Set (VF (M := M))) (hPair : nativeVFPairDomain A = X ×ˢ Y) :
    A = nativeUnaryProductDomain (nativeVFCoordinateDomain A 0) (nativeVFCoordinateDomain A 1) := by
  apply native_rectangle_projection_factorization A
  intro a b
  have ha := (mem_native_vf_pair_domain A a.val).mpr a.property
  have hb := (mem_native_vf_pair_domain A b.val).mpr b.property
  have ha' := (congrArg (fun R => twoVFPointPairEquiv a.val ∈ R) hPair).mp ha
  have hb' := (congrArg (fun R => twoVFPointPairEquiv b.val ∈ R) hPair).mp hb
  apply (mem_native_vf_pair_domain A _).mp
  exact (congrArg (fun R => twoVFPointPairEquiv
    (show Point (M := M) 2 0 from (![vfAt a.val 0,vfAt b.val 1],Fin.elim0)) ∈ R) hPair).mpr ⟨ha'.1,hb'.2⟩

end IntegrationInACVF.Section7
