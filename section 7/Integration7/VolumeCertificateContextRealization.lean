import Integration7.VolumeCertificateRealizationOnRows
import Integration7.VolumeSchemaRowExtension
import Integration7.FiniteVolumeParameterContexts

/-! A valid certificate compares any actual endpoint row interpretations
after a finite internal base extension. Its chart is still exactly the
original formula and is independent of the auxiliary exception tuple. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem GammaRVVolumeIsoCertificateSchema.realizeOn
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (F : GammaRVVolumeIsoCertificateSchema B p U.underlying.obj.arity V.underlying.obj.arity k sp)
    (z : Fin p → M) (hz : F.valid z)
    (P : RVVolumeSchemaRow U F.source z) (Q : RVVolumeSchemaRow V F.target z)
    (hB : B.real ⊆ (C.base : Set M)) (hzC : Set.range z ⊆ (C.base : Set M)) :
    ∃ (T : BaseContext M) (hCT : (C.base : Set M) ⊆ (T.base : Set M))
      (e : RVVolumeIso (U.extend hCT) (V.extend hCT)),
      ∀ x y, Fin.append (Fin.append z x) y ∈ F.chart ↔
        ∃ u : (U.extend hCT).essential.obj.domain,
          rvValues u.val = x ∧ rvValues (finiteIsoMap e.iso u).val = y := by
  obtain ⟨y,hy,hRV⟩ := hz.2.2.2.2
  obtain ⟨E⟩ := F.exception.realize (Fin.append z y) hy
  have hΓ := gamma_rv_tuple_relation_specialize sp z hz.1.1.1 F.chart_definable
  obtain ⟨d,t,hR⟩ := gamma_rv_relation_real_specialize hΓ
  obtain ⟨EE,hEE,hEcodes⟩ := E.finite_extra
  let Z := (EE ∪ Set.range (rawTuple t)) ∪ Set.range y
  have hZ : Z.Finite := (hEE.union (Set.finite_range _)).union (Set.finite_range _)
  let T := finiteVolumeParameterContext C Z hZ
  have hCT : (C.base : Set M) ⊆ (T.base : Set M) :=
    fun _ hx => finiteVolumeParameterContext_contains C Z hZ (Or.inl hx)
  have hCover : (B.real ∪ Set.range z) ∪ Z ⊆ (T.base : Set M) := by
    intro x hx
    rcases hx with (hx | hx) | hx
    · exact hCT (hB hx)
    · exact hCT (hzC hx)
    · exact finiteVolumeParameterContext_contains C Z hZ (Or.inr hx)
  have hE : E.codes ⊆ (T.base : Set M) := by
    rw [hEcodes]
    intro x hx
    apply hCover
    rcases hx with (hx | ⟨i,rfl⟩) | hx
    · exact Or.inl (Or.inl hx)
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using
          (show z i ∈ (B.real ∪ Set.range z) ∪ Z from Or.inl (Or.inr (Set.mem_range_self i)))
      · simpa only [Fin.append_right] using
          (show y i ∈ (B.real ∪ Set.range z) ∪ Z from Or.inr (Or.inr (Set.mem_range_self i)))
    · exact Or.inr (Or.inl (Or.inl hx))
  have hCode : (B.real ∪ Set.range z) ∪ Set.range (rawTuple t) ⊆ (T.base : Set M) := by
    intro x hx
    exact hCover (hx.elim Or.inl (fun hx => Or.inr (Or.inl (Or.inr hx))))
  have hRel := (canonicalRawRVRelation hc _ hR).mono _ _ hCode
  have hRel' : (rawRVSpace (M := M) U.underlying.obj.arity).RelationDefinable
      (rawRVSpace (M := M) V.underlying.obj.arity) (T.base : Set M)
      (fun x y => Fin.append (Fin.append z (rvValues x)) (rvValues y) ∈ F.chart) := hRel
  obtain ⟨e,he⟩ := GammaRVVolumeIsoCertificateSchema.realizeOnRows
    (U := U.extend hCT) (V := V.extend hCT) hc T F z hz (P.extend hCT) (Q.extend hCT) y hRV E hE hRel'
  exact ⟨T,hCT,e,he⟩

end IntegrationInACVF.Section7
