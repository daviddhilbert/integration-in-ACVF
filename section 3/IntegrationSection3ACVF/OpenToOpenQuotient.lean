import IntegrationSection3ACVF.MaximalOpenClasses

/-! Open-to-open bijections preserve the equivalence relations whose
fibres are the actual maximal open balls of their domains. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF.MaximalOpenClasses
open IntegrationInACVF.Section3ACVF.CanonicalBallSupport

namespace IntegrationInACVF.Section3ACVF.OpenToOpenQuotient

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def fibre {Q : Type*} (A : Set M) (p : M → Q) (t : Q) : Set M := {x | x ∈ A ∧ p x = t}

theorem maximal_eq_of_inter {A D E : Set M} (hD : IsMaximal A D) (hE : IsMaximal A E)
    (hm : (D ∩ E).Nonempty) : D = E := by
  have hd : IsBall D := by
    rcases hD.1 with hv | ⟨a,α,rfl⟩
    · exact Or.inl hv
    · exact BallEnlargementGeometry.gammaBall_isBall a α true
  have he : IsBall E := by
    rcases hE.1 with hv | ⟨a,α,rfl⟩
    · exact Or.inl hv
    · exact BallEnlargementGeometry.gammaBall_isBall a α true
  rcases encodedBalls_laminar D hd E he with hde | hed | hdis
  · exact Set.Subset.antisymm hde (hD.2.2 E hE.1 hde hE.2.1)
  · exact Set.Subset.antisymm (hE.2.2 D hD.1 hed hD.2.1) hed
  · obtain ⟨x,hxD,hxE⟩ := hm
    exact (Set.disjoint_left.mp hdis hxD hxE).elim

theorem same_fibres {Q R : Type*} {A B : Set M} (f : M → M)
    (hbij : Set.BijOn f A B) (hoo : OpenToOpen A f) (p : M → Q) (q : M → R)
    (hp : ∀ x ∈ A, IsMaximal A (fibre A p (p x)))
    (hq : ∀ y ∈ B, IsMaximal B (fibre B q (q y)))
    (x y : M) (hx : x ∈ A) (hy : y ∈ A) : p x = p y ↔ q (f x) = q (f y) := by
  have hxD : x ∈ fibre A p (p x) := ⟨hx,rfl⟩
  have hfxE : f x ∈ fibre B q (q (f x)) := ⟨hbij.1 hx,rfl⟩
  have hImage : f '' fibre A p (p x) = fibre B q (q (f x)) :=
    maximal_eq_of_inter (image_maximal f hbij hoo (hp x hx)) (hq (f x) (hbij.1 hx))
      ⟨f x,⟨x,hxD,rfl⟩,hfxE⟩
  constructor
  · intro he
    have hyD : y ∈ fibre A p (p x) := ⟨hy,he.symm⟩
    have hfyE : f y ∈ fibre B q (q (f x)) :=
      (Set.ext_iff.mp hImage (f y)).mp ⟨y,hyD,rfl⟩
    exact hfyE.2.symm
  · intro he
    have hfyE : f y ∈ fibre B q (q (f x)) := ⟨hbij.1 hy,he.symm⟩
    obtain ⟨z,hz,hfz⟩ := (Set.ext_iff.mp hImage (f y)).mpr hfyE
    have hzy : z = y := hbij.2.1 hz.1 hy hfz
    exact hz.2.symm.trans (congrArg p hzy)

end IntegrationInACVF.Section3ACVF.OpenToOpenQuotient
