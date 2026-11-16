module

public import IntegrationSection6.GammaVFParameterBases

@[expose] public section

/-! A sorted pure VF locus is the same actual Gamma-definable point
locus with its empty RV tuple; no new parameters are chosen. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p : ℕ}

theorem gamma_pure_vf_locus {R : Set (Fin p → M)}
    (hR : DefinableOverBase B (fun _ => .vf) R) :
    GammaSetDefinable B {q : Point (M := M) p 0 | vfValues q.1 ∈ R} := by
  have he : rawVFParameter '' {q : Point (M := M) p 0 | vfValues q.1 ∈ R} = R := by
    ext z
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact hq
    · intro hz
      let x : Fin p → VFType (M := M) := fun j => ⟨z j,hR.proper z hz j⟩
      exact ⟨(x,Fin.elim0),hz,rfl⟩
  have h : DefinableOverBase B (fun _ : Fin p => .vf)
      (rawVFParameter '' {q : Point (M := M) p 0 | vfValues q.1 ∈ R}) := he.symm ▸ hR
  change DefinableOverBase B (fun _ : Fin p => .vf)
    ((fun q : Point (M := M) p 0 => fun j => (q.1 j).val) ''
      {q : Point (M := M) p 0 | vfValues q.1 ∈ R}) at h
  simpa only [GammaSetDefinable,gammaPointSort_vf_zero,gammaPointCode_vf_zero,Nat.add_zero] using h

end IntegrationInACVF.Section7.HK
