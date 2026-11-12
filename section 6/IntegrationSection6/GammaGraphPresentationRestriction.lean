import IntegrationSection6.GammaPresentationTotalVolume

/-! Restrict an actual finite graph presentation to an original-Gamma
subdomain. The new internal code set still adds only finitely many names;
the full volume graph remains over the original base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a k : ℕ}
variable {D E : Set (Fin a → RV (M := M))}
variable {R : (Fin a → RV (M := M)) → (Fin k → RV (M := M)) → Prop}

theorem GammaFiniteGraphPresentation.exists_restrictDomain (P : GammaFiniteGraphPresentation B a k D R)
    (hED : E ⊆ D) (hE : GammaSetDefinable B {x : Point (M := M) 0 a | x.2 ∈ E}) :
    Nonempty (GammaFiniteGraphPresentation B a k E (fun x y => x ∈ E ∧ P.totalVolume x = y)) := by
  have hV : GammaGraphDefinable B (fun (x : Point (M := M) 0 a) (y : Point (M := M) 0 k) =>
      x.2 ∈ E ∧ P.totalVolume x.2 = y.2) := by
    apply GammaGraphDefinable.congr ((gammaLogicInput B).restrict_graph hE P.totalVolume_definable)
    intro x y
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hED h.1,h.2⟩⟩
  apply exists_gammaFiniteGraphPresentation hE hV
  · intro x
    exact ⟨P.totalVolume x.val,⟨x.property,rfl⟩,fun y hy => hy.2.symm⟩
  · intro y
    apply (P.totalVolume_finite_fibres y).of_injOn (f := fun x : E => x.val)
    · intro x hx
      exact ⟨hED x.property,hx.2⟩
    · exact fun x hx x' hx' he => Subtype.ext he

def GammaFiniteGraphPresentation.restrictDomain (P : GammaFiniteGraphPresentation B a k D R)
    (E : Set (Fin a → RV (M := M))) (hED : E ⊆ D)
    (hE : GammaSetDefinable B {x : Point (M := M) 0 a | x.2 ∈ E}) :
    GammaFiniteGraphPresentation B a k E (fun x y => x ∈ E ∧ P.totalVolume x = y) :=
  Classical.choice (P.exists_restrictDomain hED hE)

theorem GammaFiniteGraphPresentation.restrictDomain_totalVolume (P : GammaFiniteGraphPresentation B a k D R)
    (E : Set (Fin a → RV (M := M))) (hED : E ⊆ D)
    (hE : GammaSetDefinable B {x : Point (M := M) 0 a | x.2 ∈ E})
    (x : Fin a → RV (M := M)) (hx : x ∈ E) :
    (P.restrictDomain E hED hE).totalVolume x = P.totalVolume x := by
  let Q := P.restrictDomain E hED hE
  obtain ⟨u,hu,hv⟩ := (Q.totalVolume_graph x (Q.totalVolume x)).mpr ⟨hx,rfl⟩
  exact ((Q.graph_iff x (Q.totalVolume x)).mp ⟨u,hu,hv⟩).2.2.symm

end IntegrationInACVF.Section6
