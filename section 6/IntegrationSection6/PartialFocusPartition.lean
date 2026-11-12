import IntegrationSection6.PartialFocusLocus
import IntegrationSection6.PullbackPartitions

/-! Exact disjoint image partition of a partial centripetal step into its
nonzero active image and its unchanged complementary pullback. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)
variable {A : SpecialTransformations.Section5.DefSet (M := M) S n m}
variable {i : Fin n} {k : Fin m} (D : Focus A i k)

def focusInactiveSet : SpecialTransformations.Section5.DefSet (M := M) S n m :=
  @SpecialTransformations.DefinableGeometry.DefSet.mk LRV M N (@pointSpace M sM hM n m) S
    (carrier A \ carrier (focusActiveSet D))
    (@SpecialTransformations.DefinableGeometry.Space.Definable.sdiff LRV M N
      (@pointSpace M sM hM n m) S _ _ (setDefinable A) (setDefinable (focusActiveSet D)))

theorem focusInactive_eta (p : Point (M := M) n m) (hp : p ∈ carrier (focusInactiveSet D)) :
    D.toFocusGeometry.eta p = p := by
  have hn : p ∉ D.withoutZero.locus := fun h => hp.2 ⟨hp.1,h⟩
  exact (D.withoutZero_eta p hp.1).symm.trans (by rw [FocusGeometry.eta,if_neg hn])

theorem partialFocus_image_partition : carrier D.etaImage =
    carrier (activeFocus D).etaImage ∪ carrier (focusInactiveSet D) := by
  ext q
  constructor
  · rintro ⟨p,hp⟩
    by_cases ha : p.val ∈ carrier (focusActiveSet D)
    · exact Or.inl ⟨⟨p.val,ha⟩,(activeFocus_eta D p.val ha).trans hp⟩
    · have he := focusInactive_eta D p.val ⟨p.property,ha⟩
      exact Or.inr ((he.symm.trans hp) ▸ (show p.val ∈ carrier (focusInactiveSet D) from ⟨p.property,ha⟩))
  · rintro (⟨p,hp⟩ | hp)
    · exact ⟨⟨p.val,p.property.1⟩,(activeFocus_eta D p.val p.property).symm.trans hp⟩
    · exact ⟨⟨q,hp.1⟩,focusInactive_eta D q hp⟩

theorem partialFocus_image_disjoint :
    Disjoint (carrier (activeFocus D).etaImage) (carrier (focusInactiveSet D)) := by
  apply Set.disjoint_left.mpr
  rintro q ⟨p,hp⟩ hq
  have he : D.etaMap ⟨p.val,p.property.1⟩ = D.etaMap ⟨q,hq.1⟩ := by
    apply Subtype.ext
    exact (activeFocus_eta D p.val p.property).symm.trans (hp.trans (focusInactive_eta D q hq).symm)
  have hpeq := congrArg (fun a : A => a.val) (D.etaMap_injective he)
  change p.val = q at hpeq
  exact hq.2 (hpeq ▸ (show p.val ∈ carrier (focusActiveSet D) from p.property))

theorem partialFocus_source_partition : carrier A =
    carrier (focusActiveSet D) ∪ carrier (focusInactiveSet D) := by
  ext p
  constructor
  · intro hp
    by_cases hc : p ∈ carrier (focusActiveSet D)
    · exact Or.inl hc
    · exact Or.inr ⟨hp,hc⟩
  · rintro (hp | hp)
    · exact hp.1
    · exact hp.1

theorem focusInactiveSet_pullback (hA : IsRVPullback (carrier A)) :
    IsRVPullback (carrier (focusInactiveSet D)) := by
  have hC := focusActiveSet_pullback D hA
  apply (isRVPullback_iff _).mpr
  intro p hp q hs
  refine ⟨(isRVPullback_iff _).mp hA p hp.1 q hs,?_⟩
  intro hq
  exact hp.2 ((mem_iff_sameRV hC hs).mpr hq)

def partialFocusRVSplit (hA : IsRVPullback (carrier A)) :
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    (@originalFocusObject M sM hM S n m A i k D) ≅
      rvCoprodObject (@originalFocusObject M sM hM S n m (@focusActiveSet M sM hM S n m A i k D) i k (@activeFocus M sM hM S n m A i k D))
        (@pullbackObject M sM hM S n m (@focusInactiveSet M sM hM S n m A i k D)) :=
  pullbackPartitionIso (partialFocus_image_partition D) (partialFocus_image_disjoint D)
    ((activeFocus D).etaImage_pullback (focusActiveSet_pullback D hA))

end IntegrationInACVF.Section6
