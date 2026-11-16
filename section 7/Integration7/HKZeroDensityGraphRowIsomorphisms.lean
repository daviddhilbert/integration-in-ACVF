import Integration7.HKZeroFamilyRowIsomorphisms
import Integration7.HKZeroFamilyHeadIntegrals
import Integration7.HKWeightedPointIsomorphismCongruence
import IntegrationSection6.VFParameterFibreIsomorphisms

/-! Exact weighted zero row isomorphisms lift to isomorphisms of their
actual density graphs, preserving the appended density coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (Point GammaIso gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {n a b : ℕ}

def zeroDensityGraphGammaIso (hc : CanonicalStructure.IsCanonical (M := M))
    (F : ZeroVFVolumeFamily C (n+1) a) :
    GammaIso (⟨(C.base : Set M),∅⟩ : Base (M := M)) F.domain.carrier
      F.fullVFObject.densityGraph.domain.carrier := by
  let f := (appendDensityMap F.fullVFObject.form).toImage
  let g := nativeMixedVolumeMap hc f
  exact ⟨Equiv.ofBijective g (native_mixed_volume_map_bijective hc f
    (appendDensityMap_toImage_bijective F.fullVFObject.form)),
    (gammaLogicInput (⟨(C.base : Set M),∅⟩ : Base (M := M))).real_map_graph g⟩

def zeroDensityGraphRowGammaIso (hc : CanonicalStructure.IsCanonical (M := M))
    (F : ZeroVFVolumeFamily C (n+1) a) (x : Fin (n+1) → VFType (M := M)) :
    GammaIso (⟨(C.base : Set M) ∪ Set.range (vfValues x),∅⟩ : Base (M := M))
      (vfParameterFibre (p := n+1) (n := 0) F.domain.carrier x)
      (vfParameterFibre (p := n+1) (n := 0) F.fullVFObject.densityGraph.domain.carrier x) :=
  gammaVFParameterFibreIso (p := n+1) (n := 0) (m := 0) (zeroDensityGraphGammaIso hc F)
    (fun _ _ => rfl) x

theorem zero_density_graph_row_gamma_iso_density
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : ZeroVFVolumeFamily C (n+1) a) (x : Fin (n+1) → VFType (M := M))
    (u : vfParameterFibre (p := n+1) (n := 0) F.domain.carrier x) :
    ((zeroDensityGraphRowGammaIso hc F x).equiv u).val.2 (Fin.last a) =
      F.form.value ⟨(Fin.append (m := n+1) (n := 0) x u.val.1,u.val.2),u.property⟩ := by
  have h := congrArg (fun q : Point (M := M) (n+1) (a+1) => q.2 (Fin.last a))
    (vfParameterRowEquiv_packed (p := n+1) (n := 0) (m := 0)
      (zeroDensityGraphGammaIso hc F) (fun _ _ => rfl) x u)
  change _ = Fin.append u.val.2 (F.form.map ⟨(Fin.append (m := n+1) (n := 0) x u.val.1,u.val.2),u.property⟩).val (Fin.last a) at h
  exact h.trans (Fin.append_right _ _ (0 : Fin 1))

theorem zero_density_graph_row_iso_of_class_eq
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : ZeroVFVolumeFamily C (n+1) a) (G : ZeroVFVolumeFamily C (n+1) b)
    (x : Fin (n+1) → VFType (M := M))
    (h : rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.rowInContext x) =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (G.rowInContext x)) :
    ∃ e : GammaIso (⟨(C.base : Set M) ∪ Set.range (vfValues x),∅⟩ : Base (M := M))
      (vfParameterFibre (p := n+1) (n := 0) F.fullVFObject.densityGraph.domain.carrier x)
      (vfParameterFibre (p := n+1) (n := 0) G.fullVFObject.densityGraph.domain.carrier x),
      ∀ u, u.val.2 (Fin.last a) = (e.equiv u).val.2 (Fin.last b) := by
  let Bx : Base (M := M) := ⟨(C.base : Set M) ∪ Set.range (vfValues x),∅⟩
  obtain ⟨e,he⟩ := zero_volume_family_row_gamma_iso hc F G x h
  let f := zeroDensityGraphRowGammaIso hc F x
  let g := zeroDensityGraphRowGammaIso hc G x
  refine ⟨((f.symm (gammaLogicInput Bx)).trans (gammaLogicInput Bx) e).trans (gammaLogicInput Bx) g,?_⟩
  intro u
  obtain ⟨v,rfl⟩ := f.equiv.surjective u
  change (f.equiv v).val.2 (Fin.last a) =
    (g.equiv (e.equiv (f.equiv.symm (f.equiv v)))).val.2 (Fin.last b)
  rw [Equiv.symm_apply_apply,zero_density_graph_row_gamma_iso_density,zero_density_graph_row_gamma_iso_density]
  obtain ⟨p,q,hp,hq,hρ⟩ := he v
  have hp' : p = ⟨(Fin.append (m := n+1) (n := 0) x v.val.1,v.val.2),v.property⟩ := Subtype.ext hp
  have hq' : q = ⟨(Fin.append (m := n+1) (n := 0) x (e.equiv v).val.1,(e.equiv v).val.2),(e.equiv v).property⟩ := Subtype.ext hq
  exact hp' ▸ hq' ▸ hρ

end IntegrationInACVF.Section7.HK
