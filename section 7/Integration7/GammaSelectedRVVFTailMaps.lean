import Integration7.NativeSelectedRVVFTailMaps
import Section5.GammaLiftRelation
import IntegrationSection5.RelativelyUnary

/-! Selected VF tail maps retain their full original-Gamma graphs and
relative unary coordinate. The added VF tuple is fixed pointwise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n a b d : ℕ}
variable {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}

theorem native_selected_rv_vf_tail_map_graph_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A B) (ρ : Fin d → Fin a) (σ : Fin d → Fin b)
    (hLabels : ∀ p : A, (f p).val.2 ∘ σ = p.val.2 ∘ ρ)
    (p : Point (M := M) (n+d) a) (q : Point (M := M) (n+d) b) :
    pointMapGraph (nativeSelectedRVVFTailMap hc f ρ σ hLabels) p q ↔
      p ∈ carrier (nativeSelectedRVVFTailLift hc A ρ) ∧
      pointMapGraph f (p.1 ∘ Fin.castAdd d,p.2) (q.1 ∘ Fin.castAdd d,q.2) ∧
      p.1 ∘ Fin.natAdd n = q.1 ∘ Fin.natAdd n := by
  constructor
  · rintro ⟨u,rfl,rfl⟩
    refine ⟨u.property,⟨nativeSelectedRVVFTailProjection hc A ρ u,rfl,?_⟩,?_⟩
    · exact (congrArg (fun r : B => r.val)
        (native_selected_rv_vf_tail_map_projection hc f ρ σ hLabels u)).symm
    · exact (native_selected_rv_vf_tail_map_tail hc f ρ σ hLabels u).symm
  · rintro ⟨hp,⟨v,hv,hf⟩,ht⟩
    let u : nativeSelectedRVVFTailLift hc A ρ := ⟨p,hp⟩
    have hProj : nativeSelectedRVVFTailProjection hc A ρ u = v := Subtype.ext hv.symm
    have hHead := congrArg (fun r : B => r.val)
      (native_selected_rv_vf_tail_map_projection hc f ρ σ hLabels u)
    rw [hProj] at hHead
    have hBoth := hHead.trans hf
    have hX := congrArg Prod.fst hBoth
    have hR := congrArg Prod.snd hBoth
    have hTail := (native_selected_rv_vf_tail_map_tail hc f ρ σ hLabels u).trans ht
    refine ⟨u,rfl,Prod.ext ?_ hR⟩
    funext i
    exact Fin.addCases (fun j => congrFun hX j) (fun j => congrFun hTail j) i

theorem gamma_native_selected_rv_vf_tail_map (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A B) (ρ : Fin d → Fin a) (σ : Fin d → Fin b)
    (hLabels : ∀ p : A, (f p).val.2 ∘ σ = p.val.2 ∘ ρ)
    (hA : GammaSetDefinable G (carrier A)) (hf : GammaGraphDefinable G (pointMapGraph f)) :
    GammaGraphDefinable G (pointMapGraph (nativeSelectedRVVFTailMap hc f ρ σ hLabels)) := by
  let L := gammaLogicInput G
  have hHead := hf.preimage_maps
    (mixedCoordinatePointMap (Fin.castAdd d) (id : Fin a → Fin a) G.real)
    (mixedCoordinatePointMap (Fin.castAdd d) (id : Fin b → Fin b) G.real)
  let Z := PresentedSet.univ (pointSpace (M := M) d 0) G.real
  have ht := (L.real_map_graph (Map.id Z)).preimage_maps
    (mixedCoordinatePointMap (Fin.natAdd n) (Fin.elim0 : Fin 0 → Fin a) G.real)
    (mixedCoordinatePointMap (Fin.natAdd n) (Fin.elim0 : Fin 0 → Fin b) G.real)
  have hTail : GammaGraphDefinable G (fun (p : Point (M := M) (n+d) a) (q : Point (M := M) (n+d) b) =>
      p.1 ∘ Fin.natAdd n = q.1 ∘ Fin.natAdd n) := by
    apply GammaGraphDefinable.congr ht
    intro p q
    constructor
    · rintro ⟨z,hz,hq⟩
      exact congrArg Prod.fst (hz.symm.trans hq)
    · intro he
      refine ⟨⟨(p.1 ∘ Fin.natAdd n,Fin.elim0),Set.mem_univ _⟩,?_,?_⟩
      · exact Prod.ext rfl (by funext j; exact j.elim0)
      · exact Prod.ext he (by funext j; exact j.elim0)
  apply GammaGraphDefinable.congr
    (L.restrict_graph (gamma_native_selected_rv_vf_tail_lift hc A ρ hA) (hHead.inter hTail))
  intro p q
  exact (native_selected_rv_vf_tail_map_graph_iff hc f ρ σ hLabels p q).symm

theorem native_selected_rv_vf_tail_map_unary_relative (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A B) (ρ : Fin d → Fin a) (σ : Fin d → Fin b)
    (hLabels : ∀ p : A, (f p).val.2 ∘ σ = p.val.2 ∘ ρ)
    (i : Fin n) (hi : UnaryRelative f i) :
    UnaryRelative (nativeSelectedRVVFTailMap hc f ρ σ hLabels) (Fin.castAdd d i) := by
  intro p j hj
  cases j using Fin.addCases with
  | left t =>
    change Fin.append _ _ (Fin.castAdd d t) = _
    rw [Fin.append_left]
    exact hi (nativeSelectedRVVFTailProjection hc A ρ p) t
      (fun he => hj (congrArg (Fin.castAdd d) he))
  | right t => exact Fin.append_right _ _ t

end IntegrationInACVF.Section7
