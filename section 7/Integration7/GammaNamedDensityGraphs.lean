import Integration7.GammaNamedVFVolumeIsos
import Integration7.DensityGraphVolumeBijections
import IntegrationSection6.GammaFamilyCoordinates
import IntegrationSection6.MixedCoordinatePointMaps

/-! Gamma graphs of VF density graphs. For a VF volume object whose density
graph is Gamma-definable over `G`, the projection from the density graph is
Gamma, and an actual VF volume bijection with a Gamma graph induces a Gamma
bijection of density graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M} {n a k : ℕ}

/-- Dropping the last RV coordinate is a real global map. -/
theorem gamma_drop_last_rv_graph :
    GammaGraphDefinable G (fun (q : Point (M := M) n (a+1)) (p : Point (M := M) n a) =>
      p = (q.1,q.2 ∘ Fin.castAdd 1)) := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    (gamma_global_map_graph (B := G) (mixedCoordinatePointMap (id : Fin n → Fin n) (Fin.castAdd 1) G.real))
  intro q p
  exact eq_comm

theorem mem_volumeDensityGraph_iff {A : DefSet (rawMixedSpace (M := M) n a) S} (ω : VolumeForm A)
    (q : Point (M := M) n (a+1)) :
    q ∈ (volumeDensityGraph ω).carrier ↔
      ∃ h : (q.1,q.2 ∘ Fin.castAdd 1) ∈ A.carrier, q = (appendDensityMap ω ⟨_,h⟩).val := by
  constructor
  · rintro ⟨p,rfl⟩
    have hp : ((appendDensityMap ω p).val.1,(appendDensityMap ω p).val.2 ∘ Fin.castAdd 1) = p.val := by
      rw [appendDensityMap_value]
      refine Prod.ext rfl ?_
      funext i
      exact Fin.append_left _ _ i
    refine ⟨hp ▸ p.property,?_⟩
    have he : (⟨_,hp ▸ p.property⟩ : A) = p := Subtype.ext hp
    rw [he]
  · rintro ⟨h,hq⟩
    exact ⟨⟨_,h⟩,hq.symm⟩

theorem VFVolumeObjectGamma.projection_graph {U : PositiveVFVolumeObject (M := M) S k}
    (hU : VFVolumeObjectGamma U G) :
    GammaGraphDefinable G (fun (q : Point (M := M) (k+1) (U.arity+1)) (p : Point (M := M) (k+1) U.arity) =>
      q ∈ (volumeDensityGraph U.form).carrier ∧ p = (q.1,q.2 ∘ Fin.castAdd 1)) :=
  (gammaLogicInput G).restrict_graph hU.densityGraph gamma_drop_last_rv_graph

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem gamma_on_density_graphs {U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    (hU : VFVolumeObjectGamma U G) (hV : VFVolumeObjectGamma V G)
    (f : VFVolumeBijection U V) (hf : GammaGraphDefinable G (vfMixedMapGraph f.map)) :
    GammaGraphDefinable G (vfMixedMapGraph (f.onDensityGraphs hc C).map) := by
  have L := gammaLogicInput G
  have h := L.comp_graph hU.projection_graph (L.comp_graph hf (L.swap_graph hV.projection_graph))
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr h
  intro q q'
  constructor
  · rintro ⟨p,⟨hq,rfl⟩,p',⟨u,hu,rfl⟩,hq',hp'⟩
    obtain ⟨hq0,hqe⟩ := (mem_volumeDensityGraph_iff U.form q).mp hq
    obtain ⟨hq'0,hq'e⟩ := (mem_volumeDensityGraph_iff V.form q').mp hq'
    refine ⟨⟨q,hq⟩,rfl,?_⟩
    have hu' : u = ⟨_,hq0⟩ := Subtype.ext hu
    subst hu'
    change ((appendDensityMap V.form).toImage
      (f.map ((appendDensityMap U.form).toImage.inverse (appendDensityMap_toImage_bijective U.form) ⟨q,hq⟩))).val = q'
    have hproj : (appendDensityMap U.form).toImage.inverse (appendDensityMap_toImage_bijective U.form) ⟨q,hq⟩ =
        ⟨_,hq0⟩ := by
      apply (appendDensityMap_toImage_bijective U.form).1
      rw [Map.apply_inverse]
      exact Subtype.ext hqe
    rw [hproj]
    have hv : (⟨_,hq'0⟩ : V.domain) = f.map ⟨_,hq0⟩ := Subtype.ext hp'.symm
    rw [hq'e,hv]
    rfl
  · rintro ⟨w,rfl,rfl⟩
    obtain ⟨hq0,hqe⟩ := (mem_volumeDensityGraph_iff U.form w.val).mp w.property
    have hproj : (appendDensityMap U.form).toImage.inverse (appendDensityMap_toImage_bijective U.form) w =
        ⟨_,hq0⟩ := by
      apply (appendDensityMap_toImage_bijective U.form).1
      rw [Map.apply_inverse]
      exact Subtype.ext hqe
    let p' := f.map ⟨_,hq0⟩
    have hval : ((f.onDensityGraphs hc C).map w).val = (appendDensityMap V.form p').val := by
      change ((appendDensityMap V.form).toImage
        (f.map ((appendDensityMap U.form).toImage.inverse (appendDensityMap_toImage_bijective U.form) w))).val = _
      rw [hproj]
      rfl
    refine ⟨_,⟨w.property,rfl⟩,p'.val,⟨⟨_,hq0⟩,rfl,rfl⟩,?_,?_⟩
    · rw [hval]
      exact ⟨p',rfl⟩
    · rw [hval,appendDensityMap_value]
      refine Prod.ext rfl ?_
      funext i
      exact (Fin.append_left _ _ i).symm

end IntegrationInACVF.Section7
