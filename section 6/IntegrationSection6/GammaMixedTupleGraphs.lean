import IntegrationSection6.GammaRVGraphRaw

/-! Full Gamma graphs with a mixed VF/RV source and a pure-RV target,
in the raw tuple layout of finite family schemata. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ}

def mixedRVGraphCoordinates (p a k : ℕ) : Fin ((p+a)+k) → Fin ((p+a)+(0+k)) :=
  Fin.addCases (Fin.castAdd (0+k)) (fun j => Fin.natAdd (p+a) (Fin.natAdd 0 j))

theorem mixedRVGraphCoordinates_code (x : Point (M := M) p a) (y : Point (M := M) 0 k) :
    Fin.append (gammaPointCode x) (gammaPointCode y) ∘ mixedRVGraphCoordinates p a k =
      Fin.append (gammaPointCode x) (fun j => (y.2 j).val) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp only [mixedRVGraphCoordinates,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,
      Fin.append_left,Fin.append_right,gammaPointCode]

theorem gamma_mixed_rv_graph_from_tuple_formula {H : Set (Fin ((p+a)+k) → M)}
    (hH : DefinableOverBase B (Fin.append (gammaPointSort p a) (fun _ : Fin k => .rv)) H) :
    GammaGraphDefinable B (fun (x : Point (M := M) p a) (y : Point (M := M) 0 k) =>
      Fin.append (gammaPointCode x) (fun j => (y.2 j).val) ∈ H) := by
  let st := Fin.append (gammaPointSort p a) (gammaPointSort 0 k)
  have h := hH.preimage_real st (mixedRVGraphCoordinates p a k)
  have hh := gamma_graph_of_sorted_formula h
  apply GammaGraphDefinable.congr hh
  intro x y
  change (_ ∈ H ∧ _ ∈ sortedUniverse st) ↔ _ ∈ H
  rw [mixedRVGraphCoordinates_code]
  constructor
  · exact And.left
  · intro hxy
    refine ⟨hxy,fun j => ?_⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [st,Fin.append_left] using gammaPointCode_proper x i
    · simpa only [st,Fin.append_right] using gammaPointCode_proper y i

def gammaMixedRawGraph (r : Point (M := M) p a → Point (M := M) 0 k → Prop) :
    Set (Fin ((p+a)+k) → M) :=
  {z | ∃ x y, r x y ∧ Fin.append (gammaPointCode x) (fun j => (y.2 j).val) = z}

theorem gammaMixedRawGraph_definable
    {r : Point (M := M) p a → Point (M := M) 0 k → Prop} (hr : GammaGraphDefinable B r) :
    DefinableOverBase B (Fin.append (gammaPointSort p a) (fun _ : Fin k => .rv)) (gammaMixedRawGraph r) := by
  have h := DefinableOverBase.image_real hr (mixedRVGraphCoordinates p a k)
  have hs : Fin.append (gammaPointSort p a) (gammaPointSort 0 k) ∘ mixedRVGraphCoordinates p a k =
      Fin.append (gammaPointSort p a) (fun _ : Fin k => SortTag.rv) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp only [mixedRVGraphCoordinates,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,
        Fin.append_left,Fin.append_right,gammaPointSort]
  rw [hs] at h
  convert h using 1
  apply Set.ext
  intro z
  constructor
  · rintro ⟨x,y,hr,hz⟩
    exact ⟨Fin.append (gammaPointCode x) (gammaPointCode y),⟨x,y,hr,rfl⟩,
      (mixedRVGraphCoordinates_code x y).trans hz⟩
  · rintro ⟨_,⟨x,y,hr,rfl⟩,hz⟩
    exact ⟨x,y,hr,(mixedRVGraphCoordinates_code x y).symm.trans hz⟩

end IntegrationInACVF.Section6
