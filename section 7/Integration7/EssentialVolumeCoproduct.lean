import Integration7.VolumeCoproduct
import Integration7.RVVolumeMorphisms
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
noncomputable section
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def coprodEssentialLeftMap (U V : PositiveRVVolumeObject (M := M) S k) :
    Map U.essential.obj.domain (U.coprod V).essential.obj.domain :=
  ((rvCoprodLeftMap U.underlying.obj V.underlying.obj).restrict
    (rvEssentialLabels_subset U.underlying.obj)).corestrict (by
      intro u
      apply (mem_rvEssentialLabels (U.coprod V).underlying.obj _).mpr
      intro i
      change ((rvCoprodObject U.underlying.obj V.underlying.obj).value
        (rvCoprodLeftMap U.underlying.obj V.underlying.obj
          ⟨u.val, rvEssentialLabels_subset U.underlying.obj u.property⟩) i).val ≠ iRVZero
      rw [rvCoprod_value_left]
      exact U.essential_nonzero u i)

def coprodEssentialRightMap (U V : PositiveRVVolumeObject (M := M) S k) :
    Map V.essential.obj.domain (U.coprod V).essential.obj.domain :=
  ((rvCoprodRightMap U.underlying.obj V.underlying.obj).restrict
    (rvEssentialLabels_subset V.underlying.obj)).corestrict (by
      intro v
      apply (mem_rvEssentialLabels (U.coprod V).underlying.obj _).mpr
      intro i
      change ((rvCoprodObject U.underlying.obj V.underlying.obj).value
        (rvCoprodRightMap U.underlying.obj V.underlying.obj
          ⟨v.val, rvEssentialLabels_subset V.underlying.obj v.property⟩) i).val ≠ iRVZero
      rw [rvCoprod_value_right]
      exact V.essential_nonzero v i)

theorem coprodEssentialLeftMap_injective (U V : PositiveRVVolumeObject (M := M) S k) :
    Function.Injective (coprodEssentialLeftMap U V) := by
  intro a b he
  exact Subtype.ext (rvLeftTag_injective V.underlying.obj.arity
    (congrArg (fun z : (U.coprod V).essential.obj.domain => z.val) he))

theorem coprodEssentialRightMap_injective (U V : PositiveRVVolumeObject (M := M) S k) :
    Function.Injective (coprodEssentialRightMap U V) := by
  intro a b he
  exact Subtype.ext (rvRightTag_injective U.underlying.obj.arity
    (congrArg (fun z : (U.coprod V).essential.obj.domain => z.val) he))

theorem coprodEssentialLeftMap_coordinates (U V : PositiveRVVolumeObject (M := M) S k)
    (u : U.essential.obj.domain) :
    (U.coprod V).essential.obj.value (coprodEssentialLeftMap U V u) = U.essential.obj.value u :=
  rvCoprod_value_left U.underlying.obj V.underlying.obj _

theorem coprodEssentialRightMap_coordinates (U V : PositiveRVVolumeObject (M := M) S k)
    (v : V.essential.obj.domain) :
    (U.coprod V).essential.obj.value (coprodEssentialRightMap U V v) = V.essential.obj.value v :=
  rvCoprod_value_right U.underlying.obj V.underlying.obj _

theorem coprodEssentialLeftMap_density (U V : PositiveRVVolumeObject (M := M) S k)
    (u : U.essential.obj.domain) :
    (U.coprod V).essentialForm.value (coprodEssentialLeftMap U V u) = U.essentialForm.value u :=
  coprod_density_left U V _

theorem coprodEssentialRightMap_density (U V : PositiveRVVolumeObject (M := M) S k)
    (v : V.essential.obj.domain) :
    (U.coprod V).essentialForm.value (coprodEssentialRightMap U V v) = V.essentialForm.value v :=
  coprod_density_right U V _

theorem coprodEssential_cover (U V : PositiveRVVolumeObject (M := M) S k)
    (w : (U.coprod V).essential.obj.domain) :
    (∃ u, coprodEssentialLeftMap U V u = w) ∨ (∃ v, coprodEssentialRightMap U V v = w) := by
  have hw : w.val ∈ (rvCoprodObject U.underlying.obj V.underlying.obj).domain.carrier := w.property.1
  rcases hw with ⟨u, hu⟩ | ⟨v, hv⟩
  · left
    have he : rvCoprodLeftMap U.underlying.obj V.underlying.obj u =
        (⟨w.val, w.property.1⟩ : (U.coprod V).underlying.obj.domain) := Subtype.ext hu
    have hn : ∀ i, (U.underlying.obj.value u i).val ≠ iRVZero := by
      intro i
      have h := (U.coprod V).essential_nonzero w i
      change ((U.coprod V).underlying.obj.value ⟨w.val, w.property.1⟩ i).val ≠ iRVZero at h
      rw [← he] at h
      change ((rvCoprodObject U.underlying.obj V.underlying.obj).value
        (rvCoprodLeftMap U.underlying.obj V.underlying.obj u) i).val ≠ iRVZero at h
      rw [rvCoprod_value_left] at h
      exact h
    have hue := (mem_rvEssentialLabels U.underlying.obj u).mpr hn
    exact ⟨⟨u.val, hue⟩, Subtype.ext hu⟩
  · right
    have he : rvCoprodRightMap U.underlying.obj V.underlying.obj v =
        (⟨w.val, w.property.1⟩ : (U.coprod V).underlying.obj.domain) := Subtype.ext hv
    have hn : ∀ i, (V.underlying.obj.value v i).val ≠ iRVZero := by
      intro i
      have h := (U.coprod V).essential_nonzero w i
      change ((U.coprod V).underlying.obj.value ⟨w.val, w.property.1⟩ i).val ≠ iRVZero at h
      rw [← he] at h
      change ((rvCoprodObject U.underlying.obj V.underlying.obj).value
        (rvCoprodRightMap U.underlying.obj V.underlying.obj v) i).val ≠ iRVZero at h
      rw [rvCoprod_value_right] at h
      exact h
    have hve := (mem_rvEssentialLabels V.underlying.obj v).mpr hn
    exact ⟨⟨v.val, hve⟩, Subtype.ext hv⟩
end IntegrationInACVF.Section7
