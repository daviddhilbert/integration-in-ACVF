import Integration7.EssentialFiniteVolumeSchemata

/-! Essential restriction of a full volume schema retains its actual
density graph and the original real/Gamma parameter base. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

private theorem tupleAppendCastAdd {α : Type} {n m : ℕ} (x : Fin n → α) (y : Fin m → α) :
    Fin.append x y ∘ Fin.castAdd m = x := funext (Fin.append_left _ _)

def essentialDensityGraph (F : GammaRVVolumeSchema B p a k sp) : Set (Fin ((p+a)+1) → M) :=
  {w | w ∈ F.density ∧ w ∘ Fin.castAdd 1 ∈ (essentialFiniteVolumeSchema F.object).domain}

theorem essentialDensityGraph_definable (F : GammaRVVolumeSchema B p a k sp) :
    DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin 1 => .rv))
      (essentialDensityGraph F) := by
  have h := F.density_definable.inter
    ((essentialFiniteVolumeSchema F.object).domain_definable.preimage_real _ (Fin.castAdd 1))
  convert h using 1
  ext w
  change (w ∈ F.density ∧ w ∘ Fin.castAdd 1 ∈ _) ↔
    (w ∈ F.density ∧ w ∘ Fin.castAdd 1 ∈ _ ∧ _)
  exact ⟨fun h => ⟨h.1,h.2,F.density_definable.proper w h.1⟩,fun h => ⟨h.1,h.2.1⟩⟩

def essentialGammaVolumeSchema (F : GammaRVVolumeSchema B p a k sp) : GammaRVVolumeSchema B p a k sp where
  object := essentialFiniteVolumeSchema F.object
  density := essentialDensityGraph F
  density_definable := essentialDensityGraph_definable F
  density_nonzero w hw := F.density_nonzero w hw.1

theorem essentialGammaVolumeSchema_valid (F : GammaRVVolumeSchema B p a k sp)
    (z : Fin p → M) (hz : F.valid z) : (essentialGammaVolumeSchema F).valid z := by
  refine ⟨essentialFiniteVolumeSchema_valid F.object z hz.1,hz.2.1,?_,?_⟩
  · intro x hx
    obtain ⟨v,hv⟩ := hx
    have hdom := hz.1.2.2.1 x v hv.1
    obtain ⟨y,hy,hunique⟩ := hz.2.2.1 x hdom
    refine ⟨y,⟨hy,?_⟩,?_⟩
    · simpa only [tupleAppendCastAdd] using
        (show Fin.append z x ∈ (essentialFiniteVolumeSchema F.object).domain from ⟨v,hv⟩)
    · intro y' hy'
      exact hunique y' hy'.1
  · intro x y hxy
    change Fin.append z x ∈ (essentialFiniteVolumeSchema F.object).domain
    simpa only [tupleAppendCastAdd] using hxy.2

theorem essentialGammaVolumeSchema_rowDensity (F : GammaRVVolumeSchema B p a k sp)
    (z : Fin p → M) (x : Fin a → CanonicalRV.RVSort M) (y : Fin 1 → CanonicalRV.RVSort M) :
    (essentialGammaVolumeSchema F).rowDensity z x y ↔
      F.rowDensity z x y ∧ x ∈ (essentialFiniteVolumeSchema F.object).rowDomain z := by
  change (_ ∧ Fin.append (Fin.append z (rvValues x)) (rvValues y) ∘ Fin.castAdd 1 ∈ _) ↔ _
  rw [tupleAppendCastAdd]
  rfl

end IntegrationInACVF.Section7
