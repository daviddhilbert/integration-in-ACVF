import Section5.GammaLift
import Section5.GammaInvariantLogic

/-! Restrict an actual Gamma isomorphism to compatible definable subsets,
without requiring a real presentation of the subsets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m k l : ℕ}
variable {A A' : Set (Point (M := M) n m)} {D D' : Set (Point (M := M) k l)}

def gammaIsoRestrict (e : GammaIso B A D) (hAA : A' ⊆ A) (hDD : D' ⊆ D)
    (hCompat : ∀ a : A, a.val ∈ A' ↔ (e.equiv a).val ∈ D')
    (hA : GammaSetDefinable B A') : GammaIso B A' D' := by
  let f (a : A') : D' := ⟨(e.equiv ⟨a.val,hAA a.property⟩).val,
    (hCompat ⟨a.val,hAA a.property⟩).mp a.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b he
      have he' : e.equiv ⟨a.val,hAA a.property⟩ = e.equiv ⟨b.val,hAA b.property⟩ :=
        Subtype.ext (congrArg (fun v : D' => v.val) he)
      exact Subtype.ext (congrArg (fun v : A => v.val) (e.equiv.injective he'))
    · intro d
      let a := e.equiv.symm ⟨d.val,hDD d.property⟩
      have ha : a.val ∈ A' := (hCompat a).mpr (by
        have he := congrArg (fun v : D => v.val) (e.equiv.apply_symm_apply ⟨d.val,hDD d.property⟩)
        exact he.symm ▸ d.property)
      exact ⟨⟨a.val,ha⟩,Subtype.ext (congrArg (fun v : D => v.val) (e.equiv.apply_symm_apply ⟨d.val,hDD d.property⟩))⟩
  refine ⟨Equiv.ofBijective f hf,?_⟩
  apply GammaGraphDefinable.congr ((gammaLogicInput B).restrict_graph hA e.graph)
  intro p q
  constructor
  · rintro ⟨hp,a,ha,hq⟩
    have he : a = ⟨p,hAA hp⟩ := Subtype.ext ha
    exact ⟨⟨p,hp⟩,rfl,(congrArg (fun v => (e.equiv v).val) he).symm.trans hq⟩
  · rintro ⟨a,ha,hq⟩
    exact ⟨ha ▸ a.property,⟨a.val,hAA a.property⟩,ha,hq⟩

end IntegrationInACVF.Section6
