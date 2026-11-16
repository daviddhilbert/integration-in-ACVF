module

public import Integration7.EqualVolumeSchemaRowGeometry
public import Integration7.GammaGeometricCommonWitnesses
public import Integration7.VolumeContextJoins
public import Integration7.VolumeSchemaRowExtension

@[expose] public section

/-! Geometric schema comparison gives actual common chains for any
specified objects realizing the full rows. Containing contexts are joined
internally, and equal-row charts retain their original Gamma base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

set_option maxHeartbeats 2400000 in
theorem GammaRVVolumeSchema.commonByGammaGeometry_on_objects
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp)
    (G : GammaRVVolumeSchema B p V.underlying.obj.arity k sp) (z : Fin p → M)
    (PU : RVVolumeSchemaRow U F z) (PV : RVVolumeSchemaRow V G z)
    (hU : VolumeObjectGamma U ⟨B.real ∪ Set.range z,B.gamma⟩)
    (hV : VolumeObjectGamma V ⟨B.real ∪ Set.range z,B.gamma⟩)
    (hBC : B.real ∪ Set.range z ⊆ (C.base : Set M))
    (h : F.commonByGammaGeometry G z) :
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      GammaVolumeBlowupEquivalent ⟨B.real ∪ Set.range z,B.gamma⟩ (D.base : Set M) k
        ⟨U.extend hCD,hU.extend hCD⟩ ⟨V.extend hCD,hV.extend hCD⟩ := by
  obtain ⟨E,A,Z,ha,hb,PA,PZ,hAZ⟩ := h
  obtain ⟨J,hCJ,hEJ⟩ := volume_context_join_exists C E
  obtain ⟨K,hJK,eA,heA⟩ := gamma_equal_volume_schema_rows_iso hc J
    (U.extend hCJ) (A.val.extend hEJ) ha.symm F z
    (PU.extend hCJ) (PA.extend hEJ) (hU.extend hCJ) (hBC.trans hCJ)
  obtain ⟨D,hKD,eZ,heZ⟩ := gamma_equal_volume_schema_rows_iso hc K
    ((V.extend hCJ).extend hJK) ((Z.val.extend hEJ).extend hJK) hb.symm G z
    ((PV.extend hCJ).extend hJK) ((PZ.extend hEJ).extend hJK)
    ((hV.extend hCJ).extend hJK) (hBC.trans (hCJ.trans hJK))
  let hCD := hCJ.trans (hJK.trans hKD)
  have hmiddle := ((hAZ.extend hEJ).extend hJK).extend hKD
  refine ⟨D,hCD,GammaVolumeBlowupEquivalent.trans hc D _ ?_
    (GammaVolumeBlowupEquivalent.trans hc D _ hmiddle ?_)⟩
  · exact GammaVolumeBlowupEquivalent.of_iso D _ (eA.extend hKD) (heA.extend hKD)
  · exact GammaVolumeBlowupEquivalent.of_iso D _ (eZ.symm hc D) (heZ.symm hc D _)

end IntegrationInACVF.Section7
