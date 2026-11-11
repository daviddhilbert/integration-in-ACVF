import IntegrationSection5.ScalarRefinementFamily

/-! One original-Gamma RV refinement simultaneously makes each output VF
coordinate constant or injective in the active source coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m u w p : ℕ}

def vfScalarPointMap (S : Set M) (n m : ℕ) (i : Fin n) :
    Map (PresentedSet.univ (pointSpace (M := M) n m) S)
      (PresentedSet.univ (pointSpace 1 0) S) :=
  Map.ofCodes _ (fun a => (![vfAt a i],Fin.elim0))
    (fun z => Sum.elim (fun _ => z (.inl i)) Fin.elim0)
    (by intro j; cases j with
        | inl j => exact rawProj S (.inl i : Fin n ⊕ Fin m)
        | inr j => exact j.elim0)
    (by intro c; exact ⟨fun _ => c.property.1 i,fun j => j.elim0⟩)
    (by intro c; refine Prod.ext ?_ (Subsingleton.elim _ _)
        funext j; fin_cases j; rfl)

theorem gamma_scalar_coordinate {G : GammaParameters.Base (M := M)}
    {A : DefSet (M := M) S n m} {B : DefSet (M := M) S u w}
    (f : Map A B) (hf : GammaGraphDefinable G (pointMapGraph f)) (i : Fin u) :
    GammaScalarGraphDefinable G (fun p y => ∃ a : A, a.val = p ∧ vfAt (f a).val i = y) := by
  let L := gammaLogicInput G
  let F := vfScalarPointMap (M := M) G.real u w i
  apply GammaGraphDefinable.congr (L.comp_graph hf (L.real_map_graph F))
  intro p q
  constructor
  · rintro ⟨z,⟨a,ha,haz⟩,b,hbz,hbq⟩
    have hba : b.val = (f a).val := hbz.trans haz.symm
    have he := congrArg (fun t : Point (M := M) 1 0 => vfAt t 0) hbq
    change vfAt b.val i = vfAt q 0 at he
    refine ⟨a,ha,?_⟩
    rwa [hba] at he
  · rintro ⟨a,ha,he⟩
    refine ⟨(f a).val,⟨a,ha,rfl⟩,⟨(f a).val,Set.mem_univ _⟩,rfl,?_⟩
    refine Prod.ext ?_ (Subsingleton.elim _ _)
    funext j
    fin_cases j
    exact he

theorem coordinate_scalar_refinement {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (A : DefSet (M := M) S (p+1) m) (hA : GammaSetDefinable G (carrier A))
    {B : DefSet (M := M) S u w} (f : Map A B)
    (hf : GammaGraphDefinable G (pointMapGraph f)) :
    ∃ d : ℕ, ∃ Q : GammaRVMap G (carrier A) d, ∃ j : Fin u → Fin d,
      ∀ i : Fin u, TaggedScalarRefinement Q (j i) (fun a => vfAt (f a).val i) := by
  obtain ⟨d,Q,j,hQ⟩ := finite_scalar_family_refinement hκ hs h00 G hsmall δ hδ
    (carrier A) hA (fun i a => vfAt (f a).val i) (gamma_scalar_coordinate f hf) Finset.univ
  exact ⟨d,Q,fun i => j ⟨i,Finset.mem_univ i⟩,fun i => hQ ⟨i,Finset.mem_univ i⟩⟩

end IntegrationInACVF.Section5
