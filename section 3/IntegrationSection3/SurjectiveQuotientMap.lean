module

public import Mathlib.Data.Set.Function

@[expose] public section

/-! A bijection preserving the exact fibres of surjective coordinate maps
induces a bijection of their actual images. Its complete graph is proved
to be the existential image of the original graph. -/

namespace IntegrationInACVF.Section3.SurjectiveQuotientMap

theorem exists_bijective_factor {X Y Q R : Type*} [Inhabited R]
    {A : Set X} {B : Set Y} {U : Set Q} {V : Set R}
    (f : X → Y) (hbij : Set.BijOn f A B) (p : X → Q) (q : Y → R)
    (hp : A.MapsTo p U ∧ A.SurjOn p U)
    (hq : B.MapsTo q V ∧ B.SurjOn q V)
    (hker : ∀ x ∈ A, ∀ y ∈ A, p x = p y ↔ q (f x) = q (f y)) :
    ∃ g : Q → R, Set.BijOn g U V ∧
      (∀ x ∈ A, g (p x) = q (f x)) ∧
      ∀ u v, (u ∈ U ∧ v = g u) ↔ ∃ x ∈ A, p x = u ∧ q (f x) = v := by
  classical
  let c : U → X := fun u => Classical.choose (hp.2 u.property)
  have hc (u : U) : c u ∈ A ∧ p (c u) = u.val := Classical.choose_spec (hp.2 u.property)
  let g : Q → R := fun u => if hu : u ∈ U then q (f (c ⟨u,hu⟩)) else default
  have hg (u : Q) (hu : u ∈ U) : g u = q (f (c ⟨u,hu⟩)) := dif_pos hu
  have hFactor (x : X) (hx : x ∈ A) : g (p x) = q (f x) := by
    rw [hg (p x) (hp.1 hx)]
    exact (hker _ (hc _).1 x hx).mp (hc _).2
  have hMap : U.MapsTo g V := by
    intro u hu
    rw [hg u hu]
    exact hq.1 (hbij.1 (hc _).1)
  have hInj : U.InjOn g := by
    intro u hu v hv he
    rw [hg u hu,hg v hv] at he
    have hEq := (hker _ (hc ⟨u,hu⟩).1 _ (hc ⟨v,hv⟩).1).mpr he
    exact (hc ⟨u,hu⟩).2.symm.trans (hEq.trans (hc ⟨v,hv⟩).2)
  have hSurj : U.SurjOn g V := by
    intro v hv
    obtain ⟨y,hy,hqv⟩ := hq.2 hv
    obtain ⟨x,hx,hfx⟩ := hbij.2.2 hy
    exact ⟨p x,hp.1 hx,(hFactor x hx).trans ((congrArg q hfx).trans hqv)⟩
  refine ⟨g,⟨hMap,hInj,hSurj⟩,hFactor,?_⟩
  intro u v
  constructor
  · rintro ⟨hu,hv⟩
    exact ⟨c ⟨u,hu⟩,(hc _).1,(hc _).2,(hg u hu).symm.trans hv.symm⟩
  · rintro ⟨x,hx,hpu,hqv⟩
    refine ⟨hpu ▸ hp.1 hx,?_⟩
    exact hqv.symm.trans ((hFactor x hx).symm.trans (congrArg g hpu))

end IntegrationInACVF.Section3.SurjectiveQuotientMap
