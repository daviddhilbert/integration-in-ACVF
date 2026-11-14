import Integration7.GammaVolumeElementaryFormulas
import Integration7.NormalizedElementaryCoordinates
import Integration7.VolumeSchemaDomainSemantics
import IntegrationSection6.GammaRawElementaryRows

/-! The elementary volume formula interprets the actual elementary
blowup object, with its coordinate program and pulled-back density. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}
variable (C : BaseContext M)
variable {U : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
variable {F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp} {z : Fin p → M}

theorem RVVolumeSchemaRow.elementary_domain_iff (P : RVVolumeSchemaRow U F z) (hF : F.valid z)
    (x : Fin (U.underlying.obj.arity+1) → CanonicalRV.RVSort M) :
    x ∈ F.elementaryFormula.object.rowDomain z ↔
      x ∈ (Section6.elementary U.underlying.obj (Fin.last k)).domain.carrier :=
  (F.object.elementary_row_domain_formula (Fin.last k) z hF.1.1 x (C.base : Set M)).trans
    ((and_congr (P.domain_iff hF _) (positiveRV_normalize (C.base : Set M) _)).trans
      (Section6.elementary_domain_formula U.underlying.obj (Fin.last k) x).symm)

theorem RVVolumeSchemaRow.elementary (P : RVVolumeSchemaRow U F z) (hF : F.valid z)
    (hAd : BlowupAdmissible U) :
    RVVolumeSchemaRow (elementaryVolumeObject C U hAd) F.elementaryFormula z := by
  constructor
  · intro x t
    change (F.object.elementaryFormula (Fin.last k)).rowVolume z x t ↔
      ∃ w : (Section6.elementary U.underlying.obj (Fin.last k)).domain,
        w.val = x ∧ ((Section6.elementary U.underlying.obj (Fin.last k)).volume w).val = t
    rw [F.object.elementary_row_volume_formula (Fin.last k) z hF.1.1 x t,
      Section6.elementary_graph_formula]
    constructor
    · rintro ⟨hx,v,hv,hg⟩
      obtain ⟨u,hu,huv⟩ := (P.volume_iff (x ∘ Fin.castAdd 1) v).mp hv
      subst v
      refine ⟨(P.elementary_domain_iff C hF x).mp hx,u,hu,?_⟩
      exact (oldVolumeParameterBlowupMap_normalize B.real (C.base : Set M) (Fin.last k)
        (Fin.append (U.underlying.obj.value u) (x ∘ Fin.natAdd U.underlying.obj.arity))).symm.trans hg
    · rintro ⟨hx,u,hu,hg⟩
      refine ⟨(P.elementary_domain_iff C hF x).mpr hx,U.underlying.obj.value u,
        (P.volume_iff _ _).mpr ⟨u,hu,rfl⟩,?_⟩
      exact (oldVolumeParameterBlowupMap_normalize B.real (C.base : Set M) (Fin.last k)
        (Fin.append (U.underlying.obj.value u) (x ∘ Fin.natAdd U.underlying.obj.arity))).trans hg
  · intro x ω
    rw [F.elementary_rowDensity z hF.1.1 x ω]
    constructor
    · rintro ⟨hρ,hx⟩
      obtain ⟨u,hu,hω⟩ := (P.density_iff (x ∘ Fin.castAdd 1) ω).mp hρ
      let c : (Section6.elementary U.underlying.obj (Fin.last k)).domain :=
        ⟨x,(P.elementary_domain_iff C hF x).mp hx⟩
      have he : Section6.elementaryProjection U.underlying.obj (Fin.last k) c = u :=
        Subtype.ext ((Section6.elementaryProjection_labels U.underlying.obj (Fin.last k) c).trans hu.symm)
      refine ⟨c,rfl,?_⟩
      change (U.form.map (Section6.elementaryProjection U.underlying.obj (Fin.last k) c)).val = ω
      rw [he]
      exact hω
    · rintro ⟨c,rfl,hρ⟩
      refine ⟨(P.density_iff _ _).mpr
        ⟨Section6.elementaryProjection U.underlying.obj (Fin.last k) c,
          Section6.elementaryProjection_labels U.underlying.obj (Fin.last k) c,?_⟩,
        (P.elementary_domain_iff C hF c.val).mpr c.property⟩
      exact hρ

end IntegrationInACVF.Section7
