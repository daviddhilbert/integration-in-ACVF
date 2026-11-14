import Integration7.GammaVolumeIsoSchemaRealization
import Integration7.FiniteVolumeParameterContexts

/-! Every valid volume-isomorphism schema row has a small containing
real context and an actual volume isomorphism realizing the original
Gamma chart. Only finitely many internal representative codes are added;
no field or VF/Gamma generation property of that extension is asserted. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

theorem GammaRVVolumeIsoSchema.realize
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeIsoSchema B p a b k sp) (z : Fin p → M) (hz : F.valid z)
    (hB : B.real ⊆ (C.base : Set M)) (hzC : Set.range z ⊆ (C.base : Set M)) :
    ∃ (P : GammaVolumeGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a (k+1)
        (F.source.object.rowDomain z) (F.source.object.rowVolume z) (F.source.rowDensity z))
      (Q : GammaVolumeGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b (k+1)
        (F.target.object.rowDomain z) (F.target.object.rowVolume z) (F.target.rowDensity z))
      (T : BaseContext M), (C.base : Set M) ⊆ (T.base : Set M) ∧
      ∃ (hP : P.finite.codes ⊆ (T.base : Set M)) (hQ : Q.finite.codes ⊆ (T.base : Set M))
        (e : RVVolumeIso (P.inContext hc T hP).toObject (Q.inContext hc T hQ).toObject),
        ∀ x y, Fin.append (Fin.append z x) y ∈ F.chart ↔
          ∃ u : (P.inContext hc T hP).toObject.essential.obj.domain,
            rvValues u.val = x ∧ rvValues (finiteIsoMap e.iso u).val = y := by
  obtain ⟨P⟩ := F.source.realize z hz.1
  obtain ⟨Q⟩ := F.target.realize z hz.2.1
  obtain ⟨E⟩ := F.exception.realize z hz.2.2.2.1
  have hΓ := gamma_rv_tuple_relation_specialize sp z hz.1.1.1 F.chart_definable
  obtain ⟨d,t,hR⟩ := gamma_rv_relation_real_specialize hΓ
  obtain ⟨PE,hPE,hPcodes⟩ := P.finite.finite_extra
  obtain ⟨QE,hQE,hQcodes⟩ := Q.finite.finite_extra
  obtain ⟨EE,hEE,hEcodes⟩ := E.finite_extra
  let Z := ((PE ∪ QE) ∪ EE) ∪ Set.range (rawTuple t)
  have hZ : Z.Finite := ((hPE.union hQE).union hEE).union (Set.finite_range _)
  let T := finiteVolumeParameterContext C Z hZ
  have hCT : (C.base : Set M) ⊆ (T.base : Set M) :=
    fun _ hx => finiteVolumeParameterContext_contains C Z hZ (Or.inl hx)
  have hCover : (B.real ∪ Set.range z) ∪ Z ⊆ (T.base : Set M) := by
    intro x hx
    rcases hx with (hx | hx) | hx
    · exact hCT (hB hx)
    · exact hCT (hzC hx)
    · exact finiteVolumeParameterContext_contains C Z hZ (Or.inr hx)
  have hP : P.finite.codes ⊆ (T.base : Set M) := by
    rw [hPcodes]
    intro x hx
    apply hCover
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl (Or.inl (Or.inl hx)))
  have hQ : Q.finite.codes ⊆ (T.base : Set M) := by
    rw [hQcodes]
    intro x hx
    apply hCover
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl (Or.inl (Or.inr hx)))
  have hE : E.codes ⊆ (T.base : Set M) := by
    rw [hEcodes]
    intro x hx
    apply hCover
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl (Or.inr hx))
  have hCode : (B.real ∪ Set.range z) ∪ Set.range (rawTuple t) ⊆ (T.base : Set M) := by
    intro x hx
    exact hCover (hx.elim Or.inl (fun hx => Or.inr (Or.inr hx)))
  have hRel := (canonicalRawRVRelation hc _ hR).mono _ _ hCode
  obtain ⟨e,he⟩ := F.realizeInContext hc T z hz P Q E hP hQ hE hRel
  exact ⟨P,Q,T,hCT,hP,hQ,e,he⟩

end IntegrationInACVF.Section7
