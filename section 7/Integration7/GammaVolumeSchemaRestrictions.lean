import Integration7.GammaRVVolumeSchemata

/-! Restricting a finite RV schema by an original-base condition on its
volume tuple. The same finite bound works, with an exact projected domain. -/

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

def restrictedVolumeGraph (F : GammaFiniteRVSchema B p a d sp) (P : Set (Fin d → M)) :
    Set (Fin ((p+a)+d) → M) :=
  {w | w ∈ F.volume ∧ w ∘ Fin.natAdd (p+a) ∈ P}

theorem restrictedVolumeGraph_definable (F : GammaFiniteRVSchema B p a d sp)
    {P : Set (Fin d → M)} (hP : DefinableOverBase B (fun _ : Fin d => .rv) P) :
    DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin d => .rv))
      (restrictedVolumeGraph F P) := by
  have h := F.volume_definable.inter (hP.preimage_real _ (Fin.natAdd (p+a)))
  convert h using 1
  ext w
  change (w ∈ F.volume ∧ w ∘ Fin.natAdd (p+a) ∈ P) ↔
    (w ∈ F.volume ∧ w ∘ Fin.natAdd (p+a) ∈ P ∧ _)
  exact ⟨fun h => ⟨h.1,h.2,F.volume_definable.proper w h.1⟩,fun h => ⟨h.1,h.2.1⟩⟩

def restrictedVolumeDomain (F : GammaFiniteRVSchema B p a d sp) (P : Set (Fin d → M)) :
    Set (Fin (p+a) → M) :=
  {w | ∃ y : Fin d → M, Fin.append w y ∈ restrictedVolumeGraph F P}

def volumeRestrictedSchema (F : GammaFiniteRVSchema B p a d sp)
    (P : Set (Fin d → M)) (hP : DefinableOverBase B (fun _ : Fin d => .rv) P) :
    GammaFiniteRVSchema B p a d sp where
  domain := restrictedVolumeDomain F P
  volume := restrictedVolumeGraph F P
  domain_definable := gamma_family_row_exists_definable _ _ (restrictedVolumeGraph_definable F hP)
  volume_definable := restrictedVolumeGraph_definable F hP
  bound := F.bound

theorem volumeRestrictedSchema_valid (F : GammaFiniteRVSchema B p a d sp)
    (P : Set (Fin d → M)) (hP : DefinableOverBase B (fun _ : Fin d => .rv) P)
    (z : Fin p → M) (hz : F.valid z) : (volumeRestrictedSchema F P hP).valid z := by
  refine ⟨hz.1,?_,?_,?_⟩
  · intro x hx
    obtain ⟨y,hy⟩ := hx
    have hdom := hz.2.2.1 x y hy.1
    obtain ⟨v,hv,hunique⟩ := hz.2.1 x hdom
    refine ⟨y,hy,?_⟩
    intro y' hy'
    exact (hunique y' hy'.1).trans (hunique y hy.1).symm
  · intro x y hxy
    exact ⟨y,hxy⟩
  · intro y hy
    obtain ⟨hfin,hbound⟩ := hz.2.2.2 y hy
    have hsub : {x : Fin a → M | Fin.append (Fin.append z x) y ∈ restrictedVolumeGraph F P} ⊆
        {x : Fin a → M | Fin.append (Fin.append z x) y ∈ F.volume} := fun _ h => h.1
    exact ⟨hfin.subset hsub,(Set.ncard_le_ncard hsub hfin).trans hbound⟩

theorem volumeRestrictedSchema_rowVolume (F : GammaFiniteRVSchema B p a d sp)
    (P : Set (Fin d → M)) (hP : DefinableOverBase B (fun _ : Fin d => .rv) P)
    (z : Fin p → M) (x : Fin a → CanonicalRV.RVSort M) (y : Fin d → CanonicalRV.RVSort M) :
    (volumeRestrictedSchema F P hP).rowVolume z x y ↔ F.rowVolume z x y ∧ rvValues y ∈ P := by
  change (_ ∧ Fin.append (Fin.append z (rvValues x)) (rvValues y) ∘ Fin.natAdd (p+a) ∈ P) ↔ _
  have he : Fin.append (Fin.append z (rvValues x)) (rvValues y) ∘ Fin.natAdd (p+a) = rvValues y :=
    funext (Fin.append_right _ _)
  rw [he]
  rfl

end IntegrationInACVF.Section7
