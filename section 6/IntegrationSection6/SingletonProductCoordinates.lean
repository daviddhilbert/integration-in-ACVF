import Section4.RVProductAssociativity
import Section4.RVProductRestrictions

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] {S : Set M} {a : ℕ}

def rvSingletonProductSubset (A : DefSet (rawRVSpace (M := M) a) S) :
    A.carrier ⊆ (rvProductDomain A (DefSet.univ (rawRVSpace 0) S)).carrier := by
  intro x hx
  apply (mem_rvProductDomain A (DefSet.univ (rawRVSpace 0) S) x).mpr
  refine ⟨x,hx,Fin.elim0,Set.mem_univ _,?_⟩
  simp only [rvAppend,Fin.append_elim0,Fin.cast_refl,Function.comp_id]

def rvSingletonProductMap (A : DefSet (rawRVSpace (M := M) a) S) :
    Map A (rvProductDomain A (DefSet.univ (rawRVSpace 0) S)) :=
  Map.inclusion (rvSingletonProductSubset A)

theorem rvSingletonProductMap_pair (A : DefSet (rawRVSpace (M := M) a) S) (u : A) :
    rvSingletonProductMap A u = rvPackPair A (DefSet.univ (rawRVSpace 0) S) u ⟨Fin.elim0,Set.mem_univ _⟩ := by
  apply Subtype.ext
  change u.val = Fin.append u.val Fin.elim0
  simp only [Fin.append_elim0,Fin.cast_refl,Function.comp_id]

theorem rvSingletonProductMap_bijective (A : DefSet (rawRVSpace (M := M) a) S) :
    Function.Bijective (rvSingletonProductMap A) := by
  constructor
  · intro u v h
    exact Subtype.ext (congrArg (fun q : rvProductDomain A (DefSet.univ (rawRVSpace 0) S) => q.val) h)
  · intro x
    obtain ⟨u,v,rfl⟩ := exists_rvPackPair A (DefSet.univ (rawRVSpace 0) S) x
    have hv : v = ⟨Fin.elim0,Set.mem_univ _⟩ := by
      apply Subtype.ext
      funext j
      exact j.elim0
    subst v
    exact ⟨u,rvSingletonProductMap_pair A u⟩

end IntegrationInACVF.Section6
