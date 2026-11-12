import IntegrationSection6.GammaIndexedIsomorphisms

/-! A graph presentation's volume function, extended by zero outside its
domain. Its restricted full Gamma graph and finite fibres are unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a k : ℕ}
variable {D : Set (Fin a → RV (M := M))}
variable {R : (Fin a → RV (M := M)) → (Fin k → RV (M := M)) → Prop}

def GammaFiniteGraphPresentation.totalVolume (P : GammaFiniteGraphPresentation B a k D R)
    (x : Fin a → RV (M := M)) : Fin k → RV (M := M) :=
  if hx : x ∈ D then (P.volume (P.domainEquiv.symm ⟨x,hx⟩)).val else fun _ => 0

theorem GammaFiniteGraphPresentation.totalVolume_graph (P : GammaFiniteGraphPresentation B a k D R)
    (x : Fin a → RV (M := M)) (y : Fin k → RV (M := M)) :
    (∃ u : P.domain, u.val = x ∧ (P.volume u).val = y) ↔ x ∈ D ∧ P.totalVolume x = y := by
  constructor
  · rintro ⟨u,hu,hv⟩
    have hx : x ∈ D := (hu ▸ u.property : x ∈
      @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M (@CanonicalStructure.normalize M sM) _ P.codes P.domain)
      |> (Set.ext_iff.mp P.domain_eq x).mp
    refine ⟨hx,?_⟩
    unfold GammaFiniteGraphPresentation.totalVolume
    rw [dif_pos hx]
    have he : P.domainEquiv.symm ⟨x,hx⟩ = u := Subtype.ext hu.symm
    rw [he]
    exact hv
  · rintro ⟨hx,hv⟩
    refine ⟨P.domainEquiv.symm ⟨x,hx⟩,rfl,?_⟩
    simpa only [GammaFiniteGraphPresentation.totalVolume,dif_pos hx] using hv

theorem GammaFiniteGraphPresentation.totalVolume_definable (P : GammaFiniteGraphPresentation B a k D R) :
    GammaGraphDefinable B (fun (x : Point (M := M) 0 a) (y : Point (M := M) 0 k) =>
      x.2 ∈ D ∧ P.totalVolume x.2 = y.2) := by
  apply GammaGraphDefinable.congr P.volume_graph
  intro x y
  exact P.totalVolume_graph x.2 y.2

theorem GammaFiniteGraphPresentation.totalVolume_finite_fibres (P : GammaFiniteGraphPresentation B a k D R)
    (y : Fin k → RV (M := M)) : {x | x ∈ D ∧ P.totalVolume x = y}.Finite := by
  have h := (P.finite_volume ⟨y,Set.mem_univ _⟩).image (fun u : P.domain => u.val)
  apply h.subset
  intro x hx
  obtain ⟨u,hu,hv⟩ := (P.totalVolume_graph x y).mpr hx
  exact ⟨u,Subtype.ext hv,hu⟩

end IntegrationInACVF.Section6
