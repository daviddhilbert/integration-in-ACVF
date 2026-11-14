import Integration7.GammaVolumeSchemaRestrictions

/-! The essential part of a finite RV schema is an original-base formula.
Its exact domain consists of labels with a nonzero volume tuple. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d : ℕ} {sp : Fin p → SortTag}

theorem nonzeroRVTuples_definable (B : Base (M := M)) (d : ℕ) :
    DefinableOverBase B (fun _ : Fin d => .rv) {v | Proper v} :=
  real_definableOverBase B _ _ ((definableOver_iff_normalized_raw B.real _ _).mpr
    ⟨proper_normalized_definable B.real,fun v hv i => by simpa only [sortEval,iRV] using (hv i).1⟩)

def essentialFiniteVolumeSchema (F : GammaFiniteRVSchema B p a d sp) : GammaFiniteRVSchema B p a d sp :=
  volumeRestrictedSchema F {v | Proper v} (nonzeroRVTuples_definable B d)

theorem essentialFiniteVolumeSchema_valid (F : GammaFiniteRVSchema B p a d sp)
    (z : Fin p → M) (hz : F.valid z) : (essentialFiniteVolumeSchema F).valid z :=
  volumeRestrictedSchema_valid F _ _ z hz

theorem essentialFiniteVolumeSchema_rowVolume (F : GammaFiniteRVSchema B p a d sp)
    (z : Fin p → M) (x : Fin a → CanonicalRV.RVSort M) (y : Fin d → CanonicalRV.RVSort M) :
    (essentialFiniteVolumeSchema F).rowVolume z x y ↔
      F.rowVolume z x y ∧ ∀ i, (y i).val ≠ iRVZero := by
  unfold essentialFiniteVolumeSchema
  rw [volumeRestrictedSchema_rowVolume]
  exact and_congr_right (fun _ =>
    ⟨fun h i => (h i).2,fun h i => ⟨(y i).property,h i⟩⟩)

theorem essentialFiniteVolumeSchema_rowDomain (F : GammaFiniteRVSchema B p a d sp)
    (z : Fin p → M) (x : Fin a → CanonicalRV.RVSort M) :
    x ∈ (essentialFiniteVolumeSchema F).rowDomain z ↔
      ∃ y : Fin d → CanonicalRV.RVSort M, F.rowVolume z x y ∧ ∀ i, (y i).val ≠ iRVZero := by
  constructor
  · rintro ⟨v,hv⟩
    have hvs (i : Fin d) : iRV (v i) := by
      simpa only [Fin.append_right,sortEval,iRV] using
        F.volume_definable.proper _ hv.1 (Fin.natAdd (p+a) i)
    let y : Fin d → CanonicalRV.RVSort M := fun i => ⟨v i,hvs i⟩
    refine ⟨y,hv.1,?_⟩
    intro i
    have h := (hv.2 i).2
    simpa only [Function.comp_apply,Fin.append_right] using h
  · rintro ⟨y,hy,hn⟩
    refine ⟨rvValues y,hy,?_⟩
    intro i
    change iRV (Fin.append (Fin.append z (rvValues x)) (rvValues y) (Fin.natAdd (p+a) i)) ∧
      Fin.append (Fin.append z (rvValues x)) (rvValues y) (Fin.natAdd (p+a) i) ≠ iRVZero
    rw [Fin.append_right]
    exact ⟨(y i).property,hn i⟩

end IntegrationInACVF.Section7
