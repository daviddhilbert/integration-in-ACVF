import Integration7.GammaFunctionRowValidity
import IntegrationSection6.GammaFiniteObjectSchemata
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure GammaRVVolumeSchema (B : Base (M := M)) (p a k : ℕ) (sp : Fin p → SortTag := fun _ => .rv) where
  object : GammaFiniteRVSchema B p a (k+1) sp
  density : Set (Fin ((p+a)+1) → M)
  density_definable : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin 1 => .rv)) density
  density_nonzero : ∀ w ∈ density,w (Fin.last (p+a)) ≠ iRVZero

variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

def GammaRVVolumeSchema.valid (F : GammaRVVolumeSchema B p a k sp) (z : Fin p → M) : Prop :=
  F.object.valid z ∧ functionMapRowValid sp F.object.domain F.density z

theorem GammaRVVolumeSchema.valid_definable (F : GammaRVVolumeSchema B p a k sp) :
    DefinableOverBase B sp {z | F.valid z} :=
  F.object.valid_definable.inter (gamma_functionMapRow_validity_definable sp
    (fun _ : Fin a => .rv) (fun _ : Fin 1 => .rv) F.object.domain_definable F.density_definable)

def GammaRVVolumeSchema.rowDensity (F : GammaRVVolumeSchema B p a k sp) (z : Fin p → M)
    (x : Fin a → CanonicalRV.RVSort M) (y : Fin 1 → CanonicalRV.RVSort M) : Prop :=
  Fin.append (Fin.append z (rvValues x)) (rvValues y) ∈ F.density

theorem GammaRVVolumeSchema.rowDensity_nonzero (F : GammaRVVolumeSchema B p a k sp)
    (z : Fin p → M) (x : Fin a → CanonicalRV.RVSort M) (y : Fin 1 → CanonicalRV.RVSort M)
    (h : F.rowDensity z x y) : (y 0).val ≠ iRVZero := by
  have h' := F.density_nonzero _ h
  change Fin.append (Fin.append z (rvValues x)) (rvValues y) (Fin.natAdd (p+a) (0 : Fin 1)) ≠ iRVZero at h'
  intro hz
  exact h' ((Fin.append_right (Fin.append z (rvValues x)) (rvValues y) 0).trans hz)

theorem GammaRVVolumeSchema.rowDensity_unique (F : GammaRVVolumeSchema B p a k sp)
    (z : Fin p → M) (hz : F.valid z) (x : F.object.rowDomain z) :
    ∃! y : Fin 1 → CanonicalRV.RVSort M,F.rowDensity z x.val y := by
  obtain ⟨v,hv,hu⟩ := hz.2.2.1 (rvValues x.val) x.property
  have hvsort (i : Fin 1) : iRV (v i) := by
    simpa only [Fin.append_right,sortEval,iRV] using F.density_definable.proper _ hv (Fin.natAdd (p+a) i)
  let y : Fin 1 → CanonicalRV.RVSort M := fun i => ⟨v i,hvsort i⟩
  refine ⟨y,hv,fun y' hy' => rvValues_injective (hu (rvValues y') hy')⟩

theorem GammaRVVolumeSchema.rowDensity_support (F : GammaRVVolumeSchema B p a k sp)
    (z : Fin p → M) (hz : F.valid z) (x : Fin a → CanonicalRV.RVSort M)
    (y : Fin 1 → CanonicalRV.RVSort M) (h : F.rowDensity z x y) : x ∈ F.object.rowDomain z :=
  hz.2.2.2 (rvValues x) (rvValues y) h
end IntegrationInACVF.Section7
