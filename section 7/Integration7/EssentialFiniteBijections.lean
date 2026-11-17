module

public import Integration7.NondegenerateFiniteIso
public import Section4.MapCorestrict

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A full definable label bijection preserving the essential loci
restricts to an actual finite-category essential isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
variable {U V : RVFiniteObject (M := M) S (k+1)}

def finiteEssentialRestrictionMap (F : Map U.obj.domain V.obj.domain)
    (h : ∀ u, u.val ∈ (rvEssentialLabels U.obj).carrier ↔
      (F u).val ∈ (rvEssentialLabels V.obj).carrier) :
    Map (rvFiniteEssential U).obj.domain (rvFiniteEssential V).obj.domain :=
  (F.restrict (rvEssentialLabels_subset U.obj)).corestrict
    (fun u => (h ⟨u.val,rvEssentialLabels_subset U.obj u.property⟩).mp u.property)

theorem finite_essential_restriction_bijective (F : Map U.obj.domain V.obj.domain)
    (hF : Function.Bijective F)
    (h : ∀ u, u.val ∈ (rvEssentialLabels U.obj).carrier ↔
      (F u).val ∈ (rvEssentialLabels V.obj).carrier) :
    Function.Bijective (finiteEssentialRestrictionMap F h) := by
  constructor
  · intro u v huv
    apply Subtype.ext
    have he : F ⟨u.val,rvEssentialLabels_subset U.obj u.property⟩ =
        F ⟨v.val,rvEssentialLabels_subset U.obj v.property⟩ :=
      Subtype.ext (congrArg (fun w : (rvFiniteEssential V).obj.domain => w.val) huv)
    exact congrArg (fun w : U.obj.domain => w.val) (hF.1 he)
  · intro v
    obtain ⟨u,hu⟩ := hF.2 ⟨v.val,rvEssentialLabels_subset V.obj v.property⟩
    have he : u.val ∈ (rvEssentialLabels U.obj).carrier := (h u).mpr (by rw [hu]; exact v.property)
    exact ⟨⟨u.val,he⟩,Subtype.ext (congrArg (fun w : V.obj.domain => w.val) hu)⟩

def finiteEssentialIsoOfFullBijection (F : Map U.obj.domain V.obj.domain)
    (hF : Function.Bijective F)
    (h : ∀ u, u.val ∈ (rvEssentialLabels U.obj).carrier ↔
      (F u).val ∈ (rvEssentialLabels V.obj).carrier) : rvFiniteEssential U ≅ rvFiniteEssential V :=
  finiteIsoOfNondegenerateBijection (finiteEssentialRestrictionMap F h)
    (finite_essential_restriction_bijective F hF h)
    (rvEssential_value_nonzero U.obj) (rvEssential_value_nonzero V.obj)

end IntegrationInACVF.Section7
