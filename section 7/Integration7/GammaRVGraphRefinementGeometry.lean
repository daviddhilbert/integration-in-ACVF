module

public import Integration7.GammaRVGraphRefinements
public import IntegrationSection5.RelativelyUnary

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual geometry of an RV graph refinement: a bijection onto its
image, unchanged VF coordinates, retained old labels, finite label fibres,
and a full original-Gamma certificate for the image. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n m d : ℕ}

def gammaRVGraphRefinement (A : DefSet (M := M) S n m)
    (P : GammaRVMap G (carrier A) d) (hNames : commonRealNames G ⊆ S) :
    DefSet (M := M) S n (m+d) := Map.image (gammaRVGraphRefinementMap A P hNames)

theorem gamma_rv_graph_refinement_bijective (A : DefSet (M := M) S n m)
    (P : GammaRVMap G (carrier A) d) (hNames : commonRealNames G ⊆ S) :
    Function.Bijective (Map.toImage (gammaRVGraphRefinementMap A P hNames)) := by
  constructor
  · intro a b he
    apply gamma_rv_graph_refinement_injective A P hNames
    have hv := congrArg Subtype.val he
    exact Subtype.ext hv
  · rintro ⟨q,a,ha⟩
    exact ⟨a,Subtype.ext ha⟩

theorem gamma_rv_graph_refinement_target_gamma (A : DefSet (M := M) S n m)
    (P : GammaRVMap G (carrier A) d) (hNames : commonRealNames G ⊆ S) :
    GammaSetDefinable G (carrier (gammaRVGraphRefinement A P hNames)) := by
  have h := (gammaLogicInput G).image_graph (gamma_rv_graph_refinement_map_gamma A P hNames)
  convert h using 1
  ext q
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a.val,a,rfl,ha⟩
  · rintro ⟨p,a,ha,hq⟩
    exact ⟨a,hq⟩

theorem gamma_rv_graph_refinement_finite_labels (A : DefSet (M := M) S n m)
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (P : GammaRVMap G (carrier A) d) (hNames : commonRealNames G ⊆ S) :
    ∀ x : Fin n → VF (M := M),
      {r : Fin (m+d) → RV (M := M) | (x,r) ∈ carrier (gammaRVGraphRefinement A P hNames)}.Finite := by
  intro x
  apply (hfin x).of_injOn (f := fun r => r ∘ Fin.castAdd d)
  · rintro r ⟨a,ha⟩
    have h := congrArg (retainVFLabels (Fin.castAdd d)) ha
    change retainVFLabels (Fin.castAdd d) (gammaRVGraphRefinementMap A P hNames a).val =
      retainVFLabels (Fin.castAdd d) (x,r) at h
    rw [gamma_rv_graph_refinement_retains_labels] at h
    change a.val = (x,r ∘ Fin.castAdd d) at h
    change (x,r ∘ Fin.castAdd d) ∈ carrier A
    exact h ▸ a.property
  · rintro r ⟨a,ha⟩ s ⟨b,hb⟩ hrs
    have hA : a = b := by
      apply Subtype.ext
      have hA := (gamma_rv_graph_refinement_retains_labels A P hNames a).symm.trans
        (congrArg (retainVFLabels (Fin.castAdd d)) ha)
      have hB := (gamma_rv_graph_refinement_retains_labels A P hNames b).symm.trans
        (congrArg (retainVFLabels (Fin.castAdd d)) hb)
      have hmid : (retainVFLabels (Fin.castAdd d) (x,r) : Point (M := M) n m) =
          retainVFLabels (Fin.castAdd d) (x,s) := Prod.ext rfl hrs
      exact hA.trans (hmid.trans hB.symm)
    subst b
    have he := ha.symm.trans hb
    exact congrArg (fun q : Point (M := M) n (m+d) => q.2) he

theorem gamma_rv_graph_refinement_unary_relative (A : DefSet (M := M) S n m)
    (P : GammaRVMap G (carrier A) d) (hNames : commonRealNames G ⊆ S) (i : Fin n) :
    UnaryRelative (Map.toImage (gammaRVGraphRefinementMap A P hNames)) i := by
  intro p j hj
  rfl

end IntegrationInACVF.Section7
