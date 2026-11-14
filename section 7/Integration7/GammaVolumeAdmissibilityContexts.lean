import Integration7.GammaVolumePresentationContexts
import Integration7.ElementaryBlowupConstruction
import IntegrationSection6.GammaAdmissibility

/-! Original-Gamma admissibility gives admissibility of the actual
volume object in any containing small real context. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a k : ℕ}
variable {D : Set (Fin a → RV (M := M))}
variable {R : (Fin a → RV (M := M)) → (Fin (k+1) → RV (M := M)) → Prop}
variable {W : (Fin a → RV (M := M)) → (Fin 1 → RV (M := M)) → Prop}

theorem GammaVolumeGraphPresentation.blowupAdmissibleInContext
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : GammaVolumeGraphPresentation B a (k+1) D R W)
    (hP : P.finite.codes ⊆ (C.base : Set M))
    (hAd : GammaAdmissible P.finite.toGamma.toGammaRVObject (Fin.last k)) :
    BlowupAdmissible (P.inContext hc C hP).toObject := by
  have hsmall : Cardinal.mk B.real < C.κ :=
    (Cardinal.mk_le_mk_of_subset (P.finite.real_contains.trans hP)).trans_lt C.small
  constructor
  · intro u
    apply (rv_nonzero_iff_raw _).mpr
    exact hAd.nonzero ⟨u.val,u.property⟩
  · intro u
    let t := (P.inContext hc C hP).underlying.obj.value u
    have hsmall' : Cardinal.mk (coordinateBase B.real (Fin.last k) t) < C.κ := by
      apply (Cardinal.mk_le_mk_of_subset (show coordinateBase B.real (Fin.last k) t ⊆
        B.real ∪ Set.range (fun j => (t j).val) from ?_)).trans_lt
          (small_union_range C.uncountable.le B.real hsmall _)
      rintro x (hx | ⟨j,_,rfl⟩)
      · exact Or.inl hx
      · exact Or.inr (Set.mem_range_self j)
    have ha := hAd.algebraic ⟨u.val,u.property⟩
    have hb := (algebraic_rv_gamma_base_iff C.uncountable.le C.saturated C.model00
      ⟨coordinateBase B.real (Fin.last k) t,B.gamma⟩ hsmall' (t (Fin.last k)).val).mp ha
    apply hb.mono
    rintro x (hx | hx)
    · exact Or.inl (hP (P.finite.real_contains hx))
    · exact Or.inr hx

end IntegrationInACVF.Section7
