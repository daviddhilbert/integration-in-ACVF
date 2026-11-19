import Integration7.GammaNamedDensityGraphs
import Integration7.GammaRealRVMaps
import IntegrationSection6.MixedCoordinatePointMaps
import IntegrationSection6.GammaFamilyCoordinates

/-! Gamma graphs of volume forms on mixed domains. For a form on a Gamma
domain, a Gamma density graph is equivalent to a Gamma graph of the form
itself (as a map to one RV coordinate). Real RV operations on one or two
coordinates have Gamma graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M} {n a : ℕ}

/-- The graph of a volume form on a mixed domain, as a relation to one RV coordinate. -/
def volumeFormGraph {A : DefSet (rawMixedSpace (M := M) n a) S} (ω : VolumeForm A) :
    Point (M := M) n a → Point (M := M) 0 1 → Prop :=
  fun p y => ∃ u : A, u.val = p ∧ (ω.map u).val = y.2

/-- Last RV coordinate as a real global map. -/
theorem gamma_last_rv_graph :
    GammaGraphDefinable G (fun (q : Point (M := M) n (a+1)) (y : Point (M := M) 0 1) =>
      y = (Fin.elim0, fun _ => q.2 (Fin.last a))) := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    (gamma_global_map_graph (B := G) (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin n)
      (fun _ : Fin 1 => Fin.last a) G.real))
  intro q y
  constructor
  · intro h
    rw [← h]
    refine Prod.ext (funext (fun i => Fin.elim0 i)) rfl
  · intro h
    rw [h]
    refine Prod.ext (funext (fun i => Fin.elim0 i)) rfl

theorem volume_form_graph_of_density_graph {A : DefSet (rawMixedSpace (M := M) n a) S}
    (ω : VolumeForm A) (hω : GammaSetDefinable G (volumeDensityGraph ω).carrier) :
    GammaGraphDefinable G (volumeFormGraph ω) := by
  have L := gammaLogicInput G
  have h := L.comp_graph (L.swap_graph (L.restrict_graph hω gamma_drop_last_rv_graph))
    (gamma_last_rv_graph (G := G) (n := n) (a := a))
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr h
  intro p y
  constructor
  · rintro ⟨x, ⟨hx, rfl⟩, rfl⟩
    obtain ⟨h0, hxe⟩ := (mem_volumeDensityGraph_iff ω x).mp hx
    refine ⟨⟨_, h0⟩, rfl, ?_⟩
    have := congrArg (fun z : Point (M := M) n (a+1) => z.2 (Fin.last a)) hxe
    change x.2 (Fin.last a) = Fin.append _ (ω.map ⟨_, h0⟩).val (Fin.natAdd a (0 : Fin 1)) at this
    rw [Fin.append_right] at this
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    exact this.symm
  · rintro ⟨u, rfl, hy⟩
    refine ⟨(appendDensityMap ω u).val, ⟨⟨u, rfl⟩, ?_⟩, ?_⟩
    · rw [appendDensityMap_value]
      refine Prod.ext rfl ?_
      funext i
      exact (Fin.append_left _ _ i).symm
    · rw [appendDensityMap_value]
      refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      change y.2 0 = Fin.append u.val.2 (ω.map u).val (Fin.natAdd a (0 : Fin 1))
      rw [Fin.append_right, ← hy]

/-- Joining a point with one RV coordinate is a real global map. -/
theorem gamma_join_rv_graph :
    GammaGraphDefinable G (fun (q : Point (M := M) n (a+1)) (pr : Point (M := M) n a) =>
      pr = (q.1, q.2 ∘ Fin.castAdd 1)) := gamma_drop_last_rv_graph

theorem density_graph_of_volume_form_graph {A : DefSet (rawMixedSpace (M := M) n a) S}
    (ω : VolumeForm A) (hω : GammaGraphDefinable G (volumeFormGraph ω)) :
    GammaSetDefinable G (volumeDensityGraph ω).carrier := by
  have L := gammaLogicInput G
  have h₁ := L.comp_graph (gamma_drop_last_rv_graph (G := G) (n := n) (a := a)) hω
  have h₂ := gamma_last_rv_graph (G := G) (n := n) (a := a)
  have h := L.image_graph (L.swap_graph (h₁.inter h₂))
  convert h using 1
  ext x
  constructor
  · intro hx
    obtain ⟨h0, hxe⟩ := (mem_volumeDensityGraph_iff ω x).mp hx
    refine ⟨(Fin.elim0, fun _ => x.2 (Fin.last a)), ⟨_, rfl, ⟨_, h0⟩, rfl, ?_⟩, rfl⟩
    have := congrArg (fun z : Point (M := M) n (a+1) => z.2 (Fin.last a)) hxe
    change x.2 (Fin.last a) = Fin.append _ (ω.map ⟨_, h0⟩).val (Fin.natAdd a (0 : Fin 1)) at this
    rw [Fin.append_right] at this
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    exact this.symm
  · rintro ⟨y, ⟨_, rfl, u, hu, hy⟩, hyx⟩
    rw [hyx] at hy
    have hmem : (x.1, x.2 ∘ Fin.castAdd 1) ∈ A.carrier := hu ▸ u.property
    refine (mem_volumeDensityGraph_iff ω x).mpr ⟨hmem, ?_⟩
    have hu' : u = ⟨_, hmem⟩ := Subtype.ext hu
    subst hu'
    rw [appendDensityMap_value]
    refine Prod.ext rfl ?_
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · change x.2 (Fin.last a) = Fin.append _ _ (Fin.natAdd a (0 : Fin 1))
      rw [Fin.append_right]
      exact (congrFun hy 0).symm
    · change x.2 (Fin.castSucc i) = Fin.append _ _ (Fin.castAdd 1 i)
      rw [Fin.append_left]
      rfl

end IntegrationInACVF.Section7
