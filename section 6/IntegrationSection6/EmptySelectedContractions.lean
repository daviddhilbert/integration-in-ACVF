import IntegrationSection6.RelativeContractions
import IntegrationSection6.FiniteGammaIsomorphisms

/-! Selecting no old RV labels recovers the ordinary finite contraction
object. This gives the literal RV[n] form of Corollary6.15. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a b : ℕ}

theorem empty_selected_fibres {p m : ℕ} (A : DefSet (M := M) S p m)
    (hfin : ∀ x : Fin p → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite) :
    ∀ (x : Fin p → VF (M := M)) (t : Fin 0 → RV (M := M)),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ Fin.elim0 = t}.Finite :=
  fun x _ => (hfin x).subset (fun _ h => h.1)

def gammaEmptySelectedContractionIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    {A : DefSet (M := M) S n a} (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    {σ : Equiv.Perm (Fin n)} (C : StandardContraction A σ) (hC : GammaProgramDefinable B C.program) :
    GammaRVIso (gammaFiniteSelectedContraction hκ hs hreal hBS hA Fin.elim0
      (empty_selected_fibres A hfin) C hC).toGammaRVObject
      (gammaFiniteContraction hκ hs hreal hBS hA hfin C hC).toGammaRVObject := by
  let U := gammaFiniteSelectedContraction hκ hs hreal hBS hA Fin.elim0 (empty_selected_fibres A hfin) C hC
  let V := gammaFiniteContraction hκ hs hreal hBS hA hfin C hC
  apply gammaIsoOfFiniteEquiv U V (Equiv.refl _) (gammaIsoRefl U).graph
  intro u
  change rawWeight (fun j => (Fin.append (rvObjectVolume C.normalizedObject u).val
    (fun j : Fin 0 => u.val (contractionOldLabelIndex C (Fin.elim0 j))) j).val) =
      rawWeight (fun j => ((rvObjectVolume C.normalizedObject u).val j).val)
  apply congrArg rawWeight
  funext j
  have h := Fin.append_left (rvObjectVolume C.normalizedObject u).val
    (fun j : Fin 0 => u.val (contractionOldLabelIndex C (Fin.elim0 j))) j
  have hj : Fin.castAdd 0 j = j := Fin.ext rfl
  rw [hj] at h
  exact congrArg Subtype.val h

theorem corollary_6_15_finite {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (hBS : B.real ⊆ S)
    (U : DefSet (M := M) S (n+1) a) (V : DefSet (M := M) S (n+1) b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hfinU : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (hfinV : ∀ x : Fin (n+1) → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier V}.Finite)
    {σ : Equiv.Perm (Fin (n+1))}
    (f : Map U V) (hf : Function.Bijective f) (hF : GammaGraphDefinable B (pointMapGraph f))
    (hi : UnaryRelative f (σ 0)) (T : StandardContraction U σ) (E : StandardContraction V σ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    GammaIsp hκ.le hs h00 hreal (gammaFiniteContraction hκ.le hs hreal hBS hU hfinU T hT)
      (gammaFiniteContraction hκ.le hs hreal hBS hV hfinV E hE) := by
  have h := corollary_6_15_uncountable hκ hs h00 hreal hgamma δ hδ hδ1 hBS U V hU hV
    Fin.elim0 Fin.elim0 (empty_selected_fibres U hfinU) (empty_selected_fibres V hfinV)
    f hf hF hi (fun _ => Subsingleton.elim _ _) T E hT hE
  exact h.corollary_6_6 (gammaIsoSymm (gammaEmptySelectedContractionIso hκ.le hs hreal hBS hU hfinU T hT))
    (gammaIsoSymm (gammaEmptySelectedContractionIso hκ.le hs hreal hBS hV hfinV E hE))

end IntegrationInACVF.Section6.FiniteRV
