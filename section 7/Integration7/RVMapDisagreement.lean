import Integration7.RVVolumeLiftIsomorphism

/-! The disagreement of two actual definable maps is definable. In
particular the candidate RV Jacobian can be compared with the density
ratio without treating the Jacobian predicate itself as first order. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {a b k : ℕ}

def rvMapDisagreement {A : DefSet (rawRVSpace (M := M) a) S}
    {B : DefSet (rawRVSpace (M := M) b) S} (f g : Map A B) :
    DefSet (rawRVSpace (M := M) a) S where
  carrier := {x | ∃ u : A, u.val = x ∧ f u ≠ g u}
  definable := by
    have h := (f.graph_definable.inter _ _ g.graph_definable).exists_right _ _
    have hd := A.definable.sdiff _ h
    convert hd using 1
    ext x
    symm
    constructor
    · rintro ⟨hx,hx'⟩
      refine ⟨⟨x,hx⟩,rfl,?_⟩
      intro he
      exact hx' ⟨(f ⟨x,hx⟩).val,⟨⟨x,hx⟩,rfl,rfl⟩,
        ⟨⟨x,hx⟩,rfl,congrArg Subtype.val he.symm⟩⟩
    · rintro ⟨u,rfl,hu⟩
      refine ⟨u.property,?_⟩
      rintro ⟨y,hf,hg⟩
      exact hu (Subtype.ext (((f.graph_apply u y).mp hf).trans ((g.graph_apply u y).mp hg).symm))

theorem rvMapDisagreement_mem {A : DefSet (rawRVSpace (M := M) a) S}
    {B : DefSet (rawRVSpace (M := M) b) S} (f g : Map A B) (u : A) :
    u.val ∈ (rvMapDisagreement f g).carrier ↔ f u ≠ g u := by
  constructor
  · rintro ⟨v,hv,h⟩
    have he : v = u := Subtype.ext hv
    rwa [he] at h
  · exact fun h => ⟨u,rfl,h⟩

def volumeJacobianDisagreement {U V : PositiveRVVolumeObject (M := M) S k}
    (e : U.essential ≅ V.essential)
    (ω : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S)) :
    DefSet (rawRVSpace (M := M) U.essential.obj.arity) S :=
  rvMapDisagreement ω (volumeRatioMap e)

theorem volumeJacobianDisagreement_mem {U V : PositiveRVVolumeObject (M := M) S k}
    (e : U.essential ≅ V.essential)
    (ω : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S))
    (u : U.essential.obj.domain) :
    u.val ∈ (volumeJacobianDisagreement e ω).carrier ↔ (ω u).val 0 ≠ volumeRatio U V e u := by
  rw [volumeJacobianDisagreement,rvMapDisagreement_mem]
  constructor
  · intro h he
    apply h
    apply Subtype.ext
    funext i
    fin_cases i
    change (ω u).val 0 = (volumeRatioMap e u).val 0
    rw [volumeRatioMap_value]
    exact he
  · intro h he
    exact h ((congrFun (congrArg Subtype.val he) 0).trans (volumeRatioMap_value e u))

end IntegrationInACVF.Section7
