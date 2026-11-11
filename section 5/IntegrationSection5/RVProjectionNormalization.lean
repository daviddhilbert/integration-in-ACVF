import IntegrationSection5.StandardContraction
import Section4.RVIsoTools

/-! Explicitly present an RV volume projection as the first coordinates.
The duplicated volume tuple is retained together with every old label;
the resulting change is an actual volume-preserving RV-category isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n l : ℕ}

/-- Prepend the selected volume coordinates and retain all original labels. -/
def prependVolumeIndex (ρ : Fin n → Fin l) : Fin (n+l) → Fin l := Fin.addCases ρ id

def prependVolumeMap (D : PresentedSet (rawRVSpace (M := M) l) S) (ρ : Fin n → Fin l) :=
  rawRVProjectionMap (prependVolumeIndex ρ) D

theorem prependVolumeMap_injective (D : PresentedSet (rawRVSpace (M := M) l) S)
    (ρ : Fin n → Fin l) : Function.Injective (prependVolumeMap D ρ) := by
  intro a b hab
  have hv := congrArg (fun q : PresentedSet.univ (rawRVSpace (n+l)) S => q.val) hab
  apply Subtype.ext
  funext j
  have h := congrFun hv (Fin.natAdd n j)
  change a.val (prependVolumeIndex ρ (Fin.natAdd n j)) = b.val (prependVolumeIndex ρ (Fin.natAdd n j)) at h
  simpa [prependVolumeIndex] using h

def firstVolumeObject (D : PresentedSet (rawRVSpace (M := M) l) S) (ρ : Fin n → Fin l) :
    @SpecialTransformations.Section4.RVObject M (@CanonicalStructure.normalize M sM) S n :=
  @SpecialTransformations.Section4.RVObject.mk M (@CanonicalStructure.normalize M sM) S n
    (n+l) (Map.image (prependVolumeMap D ρ))
    (rawRVProjectionMap (Fin.castAdd l) (Map.image (prependVolumeMap D ρ)))

def selectedVolumeObject (D : PresentedSet (rawRVSpace (M := M) l) S) (ρ : Fin n → Fin l) :
    @SpecialTransformations.Section4.RVObject M (@CanonicalStructure.normalize M sM) S n :=
  @SpecialTransformations.Section4.RVObject.mk M (@CanonicalStructure.normalize M sM) S n
    l D (rawRVProjectionMap ρ D)

def toFirstVolume (D : PresentedSet (rawRVSpace (M := M) l) S) (ρ : Fin n → Fin l) :
    Map (rvObjectDomain (selectedVolumeObject D ρ)) (rvObjectDomain (firstVolumeObject D ρ)) :=
  Map.toImage (prependVolumeMap D ρ)

theorem toFirstVolume_bijective (D : PresentedSet (rawRVSpace (M := M) l) S)
    (ρ : Fin n → Fin l) : Function.Bijective (toFirstVolume D ρ) := by
  constructor
  · intro a b hab
    have hv := congrArg (fun q : rvObjectDomain (firstVolumeObject D ρ) => q.val) hab
    exact prependVolumeMap_injective D ρ (Subtype.ext hv)
  · rintro ⟨q,a,ha⟩
    exact ⟨a,Subtype.ext ha⟩

theorem toFirstVolume_volume (D : PresentedSet (rawRVSpace (M := M) l) S)
    (ρ : Fin n → Fin l) (a : rvObjectDomain (selectedVolumeObject D ρ)) :
    (rvObjectVolume (firstVolumeObject D ρ) (toFirstVolume D ρ a)).val =
      (rvObjectVolume (selectedVolumeObject D ρ) a).val := by
  funext i
  change a.val (prependVolumeIndex ρ (Fin.castAdd l i)) = a.val (ρ i)
  exact congrArg a.val (@Fin.addCases_left n l (fun _ => Fin l) ρ id i)

/-- Both RV morphism conditions and the inverse laws follow from exact volume equality. -/
def firstVolumeIso (D : PresentedSet (rawRVSpace (M := M) l) S) (ρ : Fin n → Fin l) :
    selectedVolumeObject D ρ ≅ firstVolumeObject D ρ :=
  @SpecialTransformations.Section4.rvIsoOfVolumePreservingBijection M
    (@CanonicalStructure.normalize M sM) S n _ _ (toFirstVolume D ρ)
    (toFirstVolume_bijective D ρ) (toFirstVolume_volume D ρ)

theorem firstVolumeObject_first (D : PresentedSet (rawRVSpace (M := M) l) S)
    (ρ : Fin n → Fin l) (u : rvObjectDomain (firstVolumeObject D ρ)) (i : Fin n) :
    (rvObjectVolume (firstVolumeObject D ρ) u).val i = u.val (Fin.castAdd l i) := rfl

theorem toFirstVolume_oldLabels (D : PresentedSet (rawRVSpace (M := M) l) S)
    (ρ : Fin n → Fin l) (a : rvObjectDomain (selectedVolumeObject D ρ)) (j : Fin l) :
    (toFirstVolume D ρ a).val (Fin.natAdd n j) = a.val j := by
  change a.val (Fin.addCases ρ id (Fin.natAdd n j)) = a.val j
  rw [Fin.addCases_right]
  rfl

end IntegrationInACVF.Section5
