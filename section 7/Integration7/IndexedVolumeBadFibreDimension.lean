import Integration7.IndexedVolumeFibreRealization
import Integration7.SmallExtendedRVExceptions

/-! The definable bad locus of a joint comparison has small parameter
fibres. Each fibre is contained in its own small-context RV exception;
parameter invariance descends the dimension bound to the original fibre. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.Section5 (RV)
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem indexedVolume_bad_fibre_dim
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (H : GammaRVVolumeIsoCertificateSchema B p a b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (hvalid : ∀ t ∈ T, H.valid (rvValues t))
    (P : H.source.IndexedPresentation BP) (Q : H.target.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (e : (P.inContext hc C hP).toObject.essential ≅ (Q.inContext hc C hQ).toObject.essential)
    (hChart : ∀ u v, indexedVolumeChartRelation H u.val v.val ↔ finiteIsoMap e u = v)
    (hB : B.real ⊆ (C.base : Set M))
    (ω : Map (P.inContext hc C hP).toObject.essential.obj.domain
      (DefSet.univ (rawRVSpace (M := M) 1) (C.base : Set M)))
    (A : DefSet (rawRVSpace (M := M) (p+a)) (C.base : Set M))
    (hA : A.carrier ⊆ (P.inContext hc C hP).toObject.essential.obj.domain.carrier)
    (hBad : ∀ u : A,
      IsRVJacobianAt (volumeCorrespondence (finiteIsoMap e)).carrier
        ((P.inContext hc C hP).toObject.essential.obj.value ⟨u.val,hA u.property⟩)
        ((Q.inContext hc C hQ).toObject.essential.obj.value (finiteIsoMap e ⟨u.val,hA u.property⟩))
        ((ω ⟨u.val,hA u.property⟩).val 0) ∧
      (ω ⟨u.val,hA u.property⟩).val 0 ≠ volumeRatio _ _ e ⟨u.val,hA u.property⟩)
    (t : Fin p → RV (M := M)) (ht : t ∈ T) : rvDim (rvTupleFibre A t) < k+1 := by
  classical
  by_cases hNZ : ∀ i, (BP.totalVolume t i).val ≠ iRVZero
  · obtain ⟨D,hS,hsmall,f,hf⟩ := exists_indexedRowVolumeIso hc C H BP P Q hP hQ hB t ht (hvalid t ht)
    let q := indexedVolumeFibreComparison hc C H BP P Q hP hQ e hChart t hNZ hS f hf
    obtain ⟨E,_,hE,hLocal⟩ := f.rv
    apply rvDim_lt_of_small_extended_exception hc C hS
      ((Cardinal.mk_le_mk_of_subset hS).trans_lt hsmall) hsmall (rvTupleFibre A t) E ?_ hE
    intro x hx
    let u : A := ⟨Fin.append t x,hx⟩
    let v : q.source.essential.obj.domain := ⟨x,indexedRow_essential_of_joint hc C P hP t x (hA hx)⟩
    by_contra hxE
    have hL := hLocal v hxE
    have hG := (hBad u).1
    have hHead := indexedVolume_correspondence_head hc C H BP P Q hP hQ e
      (fun u => (hChart u (finiteIsoMap e u)).mpr rfl)
    have he := q.jacobian_eq_ratio hHead v hL hG
    exact (hBad u).2 he
  · have hEmpty : (rvTupleFibre A t).carrier = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have h := (indexedVolume_essential_domain_iff hc C P hP (fun t ht => (hvalid t ht).1)
        (Fin.append t x)).mp (hA hx)
      apply hNZ
      simpa only [indexedLeft,Function.comp_def,Fin.append_left] using h.2.1
    have hFin : (rvTupleFibre A t).carrier.Finite := hEmpty ▸ Set.finite_empty
    rw [(rvDim_eq_zero_iff_finite _).mpr hFin]
    exact Nat.zero_lt_succ k

end IntegrationInACVF.Section7
