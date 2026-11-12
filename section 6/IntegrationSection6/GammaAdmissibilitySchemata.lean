import IntegrationSection6.SortedCoordinatePredicates
import IntegrationSection6.GammaAdmissibilityFromSlices

/-! Admissibility witness schemata use the checked finite-slice criterion,
with a fixed finite bound and a definable nonzero locus. Every valid row
is admissible over its actual named real/Gamma parameter base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

structure GammaFiniteAdmissibilitySchema (B : Base (M := M)) (p a k : ℕ) (sp : Fin p → SortTag := fun _ => .vf) where
  object : GammaFiniteRVSchema B p a k sp
  coordinate : Fin k
  bound : ℕ

variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

def GammaFiniteAdmissibilitySchema.valid (F : GammaFiniteAdmissibilitySchema B p a k sp)
    (z : Fin p → M) : Prop :=
  F.object.valid z ∧
  (∀ r : Fin k → M, Fin.append z r ∈ tupleVolumeImage F.object.volume → r F.coordinate ≠ iRVZero) ∧
  (∀ t : Fin k → M, (∀ j, sortEval SortTag.rv (t j)) →
    {r | Fin.append z r ∈ tupleVolumeImage F.object.volume ∧ ∀ j, j ≠ F.coordinate → r j = t j}.Finite ∧
    {r | Fin.append z r ∈ tupleVolumeImage F.object.volume ∧ ∀ j, j ≠ F.coordinate → r j = t j}.ncard ≤ F.bound)

theorem GammaFiniteAdmissibilitySchema.valid_definable (F : GammaFiniteAdmissibilitySchema B p a k sp) :
    DefinableOverBase B sp {z | F.valid z} := by
  let sr : Fin k → SortTag := fun _ => .rv
  let D := tupleVolumeImage F.object.volume
  have hD := F.object.volume_image_definable
  have hNZ := real_definableOverBase B (Fin.append sp sr) _
    (sorted_coordinate_nonzero_definable B.real (Fin.append sp sr) (Fin.natAdd p F.coordinate))
  have hn := gamma_family_row_subset_definable sp sr hD hNZ
  have hb := gamma_label_slice_bound_definable sp F.bound hD F.coordinate
  have h := F.object.valid_definable.inter (hn.inter hb)
  convert h using 1
  apply Set.ext
  intro z
  constructor
  · rintro ⟨ho,hn,hb⟩
    refine ⟨ho,⟨ho.1,?_⟩,ho.1,hb⟩
    intro r hr
    refine ⟨hD.proper _ hr,?_⟩
    simpa only [Fin.append_right] using hn r hr
  · rintro ⟨ho,⟨_,hn⟩,_,hb⟩
    refine ⟨ho,?_,hb⟩
    intro r hr
    have hh := (hn r hr).2
    simpa only [Fin.append_right] using hh

theorem GammaFiniteAdmissibilitySchema.admissible (F : GammaFiniteAdmissibilitySchema B p a k sp)
    (z : Fin p → M) (hz : F.valid z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (F.object.rowDomain z) (F.object.rowVolume z)) :
    GammaAdmissible P.toGamma.toGammaRVObject F.coordinate := by
  have hVol (u : P.domain) :
      Fin.append z (fun j => (gammaVolumeValue P.toGamma.toGammaRVObject u j).val) ∈
        tupleVolumeImage F.object.volume := by
    apply (tupleVolumeImage_append_iff F.object.volume z _).mpr
    exact ⟨fun j => (u.val j).val,((P.graph_iff u.val (P.volume u).val).mp ⟨u,rfl,rfl⟩).2⟩
  apply gammaAdmissible_of_finite_label_slices
  · intro u
    exact hz.2.1 _ (hVol u)
  · intro t
    have ht : ∀ j, sortEval SortTag.rv (t j).val := by
      intro j
      simpa only [sortEval,iRV] using (t j).property
    have hf := (hz.2.2 (fun j => (t j).val) ht).1
    apply hf.of_injOn (f := fun r : Fin k → CanonicalRV.RVSort M => fun j => (r j).val)
    · rintro r ⟨⟨u,hu⟩,hr⟩
      refine ⟨?_,fun j hj => congrArg Subtype.val (hr j hj)⟩
      rw [← hu]
      exact hVol u
    · intro r hr s hs he
      funext j
      apply Subtype.ext
      exact congrFun he j

theorem GammaFiniteAdmissibilitySchema.realize (F : GammaFiniteAdmissibilitySchema B p a k sp)
    (z : Fin p → M) (hz : F.valid z) :
    ∃ P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (F.object.rowDomain z) (F.object.rowVolume z), GammaAdmissible P.toGamma.toGammaRVObject F.coordinate := by
  obtain ⟨P⟩ := F.object.realize z hz.1
  exact ⟨P,F.admissible z hz P⟩

end IntegrationInACVF.Section6
