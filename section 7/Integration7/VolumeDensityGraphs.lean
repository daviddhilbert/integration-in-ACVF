import Integration7.VFVolumeBijections
import Section4.ProductBijections
import Section4.ProductRearrangement
import Section4.RVAppend

/-! The actual density graph A_omega used before taking standard
contractions. It adds one RV label, preserves VF coordinates, and is
volume-isomorphic to the original positive VF object. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a k : ℕ}

def appendDensityMap {A : DefSet (rawMixedSpace (M := M) n a) S} (ω : VolumeForm A) :
    Map A (DefSet.univ (rawMixedSpace (M := M) n (a + 1)) S) := by
  let X := DefSet.univ (rawVFSpace (M := M) n) S
  let R := DefSet.univ (rawRVSpace (M := M) a) S
  let T := DefSet.univ (rawRVSpace (M := M) 1) S
  let F := (Map.id A).pair ω.map
  have h : (A.prod T).carrier ⊆ ((X.prod R).prod T).carrier :=
    fun _ _ => ⟨⟨Set.mem_univ _, Set.mem_univ _⟩, Set.mem_univ _⟩
  let G := (Map.prodAssoc X R T).comp ((Map.inclusion h).comp F)
  exact (Map.prodUnivMap (Map.id X) (rvAppendMap S a 1)).comp G.toUniv

@[simp] theorem appendDensityMap_value {A : DefSet (rawMixedSpace (M := M) n a) S}
    (ω : VolumeForm A) (p : A) :
    (appendDensityMap ω p).val = (p.val.1, Fin.append p.val.2 (ω.map p).val) := rfl

theorem appendDensityMap_injective {A : DefSet (rawMixedSpace (M := M) n a) S}
    (ω : VolumeForm A) : Function.Injective (appendDensityMap ω) := by
  intro p q he
  have hv := congrArg (fun r : DefSet.univ (rawMixedSpace (M := M) n (a + 1)) S => r.val) he
  change (p.val.1, Fin.append p.val.2 (ω.map p).val) =
    (q.val.1, Fin.append q.val.2 (ω.map q).val) at hv
  have hx : p.val.1 = q.val.1 := congrArg
    (fun z : (Fin n → VFType (M := M)) × (Fin (a + 1) → CanonicalRV.RVSort M) => z.1) hv
  have hr : p.val.2 = q.val.2 := by
    funext i
    have he' := congrArg
      (fun z : (Fin n → VFType (M := M)) × (Fin (a + 1) → CanonicalRV.RVSort M) =>
        z.2 (Fin.castAdd 1 i)) hv
    simpa only [Fin.append_left] using he'
  exact Subtype.ext (Prod.ext hx hr)

def volumeDensityGraph {A : DefSet (rawMixedSpace (M := M) n a) S} (ω : VolumeForm A) :
    DefSet (rawMixedSpace (M := M) n (a + 1)) S := (appendDensityMap ω).image

theorem appendDensityMap_toImage_bijective {A : DefSet (rawMixedSpace (M := M) n a) S}
    (ω : VolumeForm A) : Function.Bijective (appendDensityMap ω).toImage := by
  constructor
  · intro p q he
    exact appendDensityMap_injective ω (Subtype.ext
      (congrArg (fun r : volumeDensityGraph ω => r.val) he))
  · rintro ⟨r, p, hp⟩
    exact ⟨p, Subtype.ext hp⟩

def densityGraphProjection {A : DefSet (rawMixedSpace (M := M) n a) S} (ω : VolumeForm A) :
    Map (volumeDensityGraph ω) A :=
  (appendDensityMap ω).toImage.inverse (appendDensityMap_toImage_bijective ω)

theorem densityGraphProjection_value {A : DefSet (rawMixedSpace (M := M) n a) S}
    (ω : VolumeForm A) (q : volumeDensityGraph ω) :
    (densityGraphProjection ω q).val = (q.val.1, q.val.2 ∘ Fin.castAdd 1) := by
  obtain ⟨p, rfl⟩ := (appendDensityMap_toImage_bijective ω).2 q
  change ((appendDensityMap ω).toImage.inverse _ ((appendDensityMap ω).toImage p)).val = _
  rw [Map.inverse_apply]
  change p.val = (p.val.1, Fin.append p.val.2 (ω.map p).val ∘ Fin.castAdd 1)
  apply Prod.ext
  · rfl
  · funext i
    exact (Fin.append_left p.val.2 (ω.map p).val i).symm

theorem densityGraphPullback_form_last {A : DefSet (rawMixedSpace (M := M) n a) S}
    (ω : VolumeForm A) (q : volumeDensityGraph ω) :
    (ω.pullback (densityGraphProjection ω)).value q = q.val.2 (Fin.last a) := by
  obtain ⟨p, rfl⟩ := (appendDensityMap_toImage_bijective ω).2 q
  change ω.value ((appendDensityMap ω).toImage.inverse _ ((appendDensityMap ω).toImage p)) = _
  rw [Map.inverse_apply]
  change (ω.map p).val 0 = Fin.append p.val.2 (ω.map p).val (Fin.last a)
  have hi : Fin.last a = Fin.natAdd a (0 : Fin 1) := rfl
  rw [hi, Fin.append_right]

def PositiveVFVolumeObject.densityGraph (U : PositiveVFVolumeObject (M := M) S k) :
    PositiveVFVolumeObject (M := M) S k where
  arity := U.arity + 1
  domain := volumeDensityGraph U.form
  finite_labels x := by
    apply (U.finite_labels x).of_injOn (f := fun r => r ∘ Fin.castAdd 1)
    · intro r hr
      let q : volumeDensityGraph U.form := ⟨(x, r), hr⟩
      have hp := (densityGraphProjection U.form q).property
      rw [densityGraphProjection_value] at hp
      exact hp
    · intro r hr s hs he
      let p : volumeDensityGraph U.form := ⟨(x, r), hr⟩
      let q : volumeDensityGraph U.form := ⟨(x, s), hs⟩
      have hpq : densityGraphProjection U.form p = densityGraphProjection U.form q :=
        Subtype.ext ((densityGraphProjection_value U.form p).trans
          ((congrArg (fun t => (x, t)) he).trans (densityGraphProjection_value U.form q).symm))
      have h := congrArg (appendDensityMap U.form).toImage hpq
      simp only [densityGraphProjection, Map.apply_inverse] at h
      exact congrArg (fun q : volumeDensityGraph U.form => q.val.2) h
  form := U.form.pullback (densityGraphProjection U.form)

theorem densityGraph_form_last (U : PositiveVFVolumeObject (M := M) S k)
    (q : U.densityGraph.domain) : U.densityGraph.form.value q = q.val.2 (Fin.last U.arity) :=
  densityGraphPullback_form_last U.form q

def volumeDensityGraphBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k) :
    VFVolumeBijection U U.densityGraph :=
  VFVolumeBijection.of_preserving_vf_and_density hc C (appendDensityMap U.form).toImage
    (appendDensityMap_toImage_bijective U.form) (fun _ => rfl) (fun p => by
      change U.form.value p = U.form.value ((appendDensityMap U.form).toImage.inverse _
        ((appendDensityMap U.form).toImage p))
      rw [Map.inverse_apply])

end IntegrationInACVF.Section7
