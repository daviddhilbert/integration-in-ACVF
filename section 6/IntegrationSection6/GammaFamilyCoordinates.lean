import IntegrationSection6.GammaRVFamilyFormulas
import IntegrationSection6.RVLabelMap
import IntegrationSection6.GammaElementaryStructure

/-! Global real coordinate maps for Gamma RV families, keeping the VF
parameter block fixed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m u v : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gamma_global_map_graph
    (f : Map (PresentedSet.univ (pointSpace (M := M) n m) B.real)
      (PresentedSet.univ (pointSpace (M := M) u v) B.real)) :
    GammaGraphDefinable B (fun p q => (f ⟨p,Set.mem_univ _⟩).val = q) := by
  apply GammaGraphDefinable.congr ((gammaLogicInput B).real_map_graph f)
  intro p q
  constructor
  · rintro ⟨x,hx,hq⟩
    have he : x = ⟨p,Set.mem_univ _⟩ := Subtype.ext hx
    exact he ▸ hq
  · exact fun h => ⟨⟨p,Set.mem_univ _⟩,rfl,h⟩

theorem gamma_global_preimage
    (f : Map (PresentedSet.univ (pointSpace (M := M) n m) B.real)
      (PresentedSet.univ (pointSpace (M := M) u v) B.real))
    {A : Set (Point (M := M) u v)} (hA : GammaSetDefinable B A) :
    GammaSetDefinable B {p | (f ⟨p,Set.mem_univ _⟩).val ∈ A} := by
  have h := (gammaLogicInput B).preimage_real f hA
  convert h using 1
  apply Set.ext
  intro p
  constructor
  · exact fun hp => ⟨⟨p,Set.mem_univ _⟩,rfl,hp⟩
  · rintro ⟨x,hx,hp⟩
    have he : x = ⟨p,Set.mem_univ _⟩ := Subtype.ext hx
    change (f ⟨p,Set.mem_univ _⟩).val ∈ A
    exact he ▸ hp

def familyOldLabelsMap (S : Set M) (p a : ℕ) :
    Map (PresentedSet.univ (pointSpace (M := M) p (a+1)) S)
      (PresentedSet.univ (pointSpace (M := M) p a) S) :=
  @mapRVLabels M sM hM p (a+1) a S
    (@selectRVTuple M N S (a+1) a (Fin.castAdd 1)
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N
        (@SpecialTransformations.Section4.rawRVSpace M N (a+1)) S))

theorem familyOldLabelsMap_value (S : Set M) (p a : ℕ)
    (x : PresentedSet.univ (pointSpace (M := M) p (a+1)) S) :
    (familyOldLabelsMap S p a x).val = (x.val.1,fun j => x.val.2 (Fin.castAdd 1 j)) := rfl

def familyNewParameterMap (S : Set M) (p a : ℕ) :
    Map (PresentedSet.univ (pointSpace (M := M) p (a+1)) S)
      (PresentedSet.univ (pointSpace (M := M) 0 1) S) :=
  @Map.comp M sM _ _ _ S _ _ _
    (rvCoordinatePointMap (Fin.natAdd a : Fin 1 → Fin (a+1)) S)
    (@pointLabels M sM hM S p (a+1))

theorem familyNewParameterMap_value (S : Set M) (p a : ℕ)
    (x : PresentedSet.univ (pointSpace (M := M) p (a+1)) S) :
    (familyNewParameterMap S p a x).val.2 = fun j => x.val.2 (Fin.natAdd a j) := by
  change (pointLabels S p (a+1) x).val.2 ∘ Fin.natAdd a = _
  rw [pointLabels_snd]
  rfl

end IntegrationInACVF.Section6
