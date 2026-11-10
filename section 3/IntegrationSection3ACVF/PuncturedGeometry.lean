import IntegrationSection3ACVF.FullBaseDefinability
import IntegrationSection3.PuncturedDecomposition

/-! Actual punctured balls and finite disjoint decomposition in ACVF.
The parent and holes are actual encoded-ball point sets. No chosen centre
is made a parameter. Equality of primitive types is a later obligation. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3.PuncturedDecomposition

namespace IntegrationInACVF.Section3ACVF.PuncturedGeometry

variable {M : Type} [sM : LRV.Structure M]

structure PuncturedBall (M : Type) [LRV.Structure M] where
  parent : Set M
  parent_ball : IsBall parent
  holes : Finset (Set M)
  holes_ball : ∀ h ∈ holes, IsBall h
  holes_proper : ∀ h ∈ holes, h ⊂ parent
  holes_disjoint : (holes : Set (Set M)).Pairwise Disjoint

def PuncturedBall.body (d : PuncturedBall M) : Set M :=
  d.parent \ {x | ∃ h ∈ d.holes, x ∈ h}

theorem PuncturedBall.body_subset_parent (d : PuncturedBall M) : d.body ⊆ d.parent :=
  fun _ hx => hx.1

variable [hM : M ⊨ Axioms.ACVF]

theorem PuncturedBall.body_subset_vf (d : PuncturedBall M) : d.body ⊆ {x | iVF x} :=
  d.body_subset_parent.trans (isBall_subset_vf d.parent d.parent_ball)

/-- The initial C-minimality step of Lemma 3.6, for every definable unary
VF set over the original real/Gamma/ball base. This does not assert that
individual pieces are definable over that base or have the same primitive type. -/
theorem definable_punctured_decomposition (B : FullBaseAtomicity.Base (M := M))
    (A : Set M) (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAVF : A ⊆ {x | iVF x}) :
    ∃ F : Finset (PuncturedBall M), (∀ d ∈ F, d.body.Nonempty) ∧
      (F : Set (PuncturedBall M)).Pairwise (fun d e => Disjoint d.body e.body) ∧
      A = {x | ∃ d ∈ F, x ∈ d.body} := by
  classical
  have hl := encodedBalls_laminar (M := M)
  have hcm (Q : Set M) := normalized_cMinimalOn (M := M) Q
  have hd : IsBall ({x : M | iVF x}) := Or.inl rfl
  have hs : HasFiniteBallSupport {b : Set M | IsBall b} A := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryParameters.finite_ball_support hcm hA hAVF
  obtain ⟨F,G,hF,hGF,hne,hdis,he,hholes⟩ := finite_punctured_decomposition hl hd hAVF hs
  let f : G → PuncturedBall M := fun b =>
    ⟨b.val,hF b.val (hGF b.property),holes F b.val,
      fun h hh => hF h (mem_holes.mp hh).1,
      fun h hh => (mem_holes.mp hh).2.1,hholes b.val b.property⟩
  have hf (b : G) : (f b).body = region F b.val :=
    (region_eq_sdiff_holes F b.val).symm
  refine ⟨G.attach.image f,?_,?_,?_⟩
  · intro d hd
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hd
    rw [hf]
    exact hne b.val b.property
  · intro d hd e he hde
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp he
    have hbc : b.val ≠ c.val := fun h => hde (congrArg f (Subtype.ext h))
    rw [hf,hf]
    exact hdis b.property c.property hbc
  · rw [he]
    ext x
    constructor
    · rintro ⟨b,hb,hx⟩
      refine ⟨f ⟨b,hb⟩,Finset.mem_image.mpr ⟨⟨b,hb⟩,Finset.mem_attach _ _,rfl⟩,?_⟩
      rwa [hf]
    · rintro ⟨d,hd,hx⟩
      obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hd
      rw [hf] at hx
      exact ⟨b.val,b.property,hx⟩

end IntegrationInACVF.Section3ACVF.PuncturedGeometry
