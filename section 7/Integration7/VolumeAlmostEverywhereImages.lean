import Integration7.VolumeAlmostEverywhere

set_option backward.isDefEq.respectTransparency false
noncomputable section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.RVAlmostEverywhere

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {a b n : ℕ}

/-- A small exceptional set stays small under a definable injection. Outside
the image the resulting assertion is vacuous. -/
theorem extend_injective
    {A : DefSet (rawRVSpace (M := M) a) S} {B : DefSet (rawRVSpace (M := M) b) S}
    (F : Map A B) (hF : Function.Injective F) {P : A → Prop}
    (hP : RVAlmostEverywhere A n P) :
    RVAlmostEverywhere B n (fun b => ∀ a, F a = b → P a) := by
  obtain ⟨D, hDA, hd, hP⟩ := hP
  let m : Map D B := F.restrict hDA
  have hm : Function.Bijective m.toImage := by
    constructor
    · intro x y he
      have hxy : F ⟨x.val, hDA x.property⟩ = F ⟨y.val, hDA y.property⟩ :=
        Subtype.ext (congrArg (fun z : m.image => z.val) he)
      exact Subtype.ext (congrArg (fun z : A => z.val) (hF hxy))
    · rintro ⟨b, a, rfl⟩
      exact ⟨a, rfl⟩
  refine ⟨m.image, ?_, (rvDim_eq_of_bijective m.toImage hm).symm.trans_lt hd, ?_⟩
  · rintro b ⟨a, rfl⟩
    exact (m a).property
  · intro b hb a hab
    apply hP a
    intro ha
    apply hb
    exact ⟨⟨a.val, ha⟩, congrArg (fun z : B => z.val) hab⟩

end IntegrationInACVF.Section7.RVAlmostEverywhere
