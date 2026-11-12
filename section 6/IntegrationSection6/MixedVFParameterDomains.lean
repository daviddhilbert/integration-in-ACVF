import IntegrationSection6.GammaPointSortedIsomorphisms
import IntegrationSection6.GammaVFParameterBases

/-! Sorted parameter/fibre coordinates for actual mixed VF/RV families. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p n a : ℕ}

def vfParameterFibre (U : Set (Point (M := M) (p+n) a)) (x : Fin p → VF (M := M)) :
    Set (Point (M := M) n a) := {q | (Fin.append x q.1,q.2) ∈ U}

def mixedVFParameterSort (p n a : ℕ) : Fin (p+(n+a)) → SortTag :=
  Fin.append (fun _ : Fin p => SortTag.vf) (gammaPointSort n a)

def mixedVFParameterDomain (U : Set (Point (M := M) (p+n) a)) : Set (Fin (p+(n+a)) → M) :=
  {w | w ∘ Fin.cast (Nat.add_assoc p n a) ∈ gammaPointCode '' U ∧ w ∈ sortedUniverse (mixedVFParameterSort p n a)}

theorem gamma_mixedVFParameterDomain (U : Set (Point (M := M) (p+n) a))
    (hU : GammaSetDefinable B U) :
    DefinableOverBase B (mixedVFParameterSort p n a) (mixedVFParameterDomain U) :=
  hU.preimage_real (mixedVFParameterSort p n a) (Fin.cast (Nat.add_assoc p n a))

theorem mixedVFParameterSort_cast :
    mixedVFParameterSort p n a ∘ Fin.cast (Nat.add_assoc p n a) = gammaPointSort (p+n) a := by
  change Fin.append (fun _ : Fin p => SortTag.vf)
    (Fin.append (fun _ : Fin n => SortTag.vf) (fun _ : Fin a => SortTag.rv)) ∘ Fin.cast (Nat.add_assoc p n a) = _
  rw [← Fin.append_assoc]
  change Fin.append (Fin.append (fun _ : Fin p => SortTag.vf) (fun _ : Fin n => SortTag.vf)) (fun _ : Fin a => SortTag.rv) =
    Fin.append (fun _ : Fin (p+n) => SortTag.vf) (fun _ : Fin a => SortTag.rv)
  congr 1
  funext j
  exact Fin.addCases (fun i => Fin.append_left _ _ i) (fun i => Fin.append_right _ _ i) j

theorem mixedVFParameterCode_append (x : Fin p → VF (M := M)) (q : Point (M := M) n a) :
    Fin.append (fun j => (x j).val) (gammaPointCode q) ∘ Fin.cast (Nat.add_assoc p n a) =
      gammaPointCode (Fin.append x q.1,q.2) := by
  have hv : (fun j => ((Fin.append x q.1) j).val) =
      Fin.append (fun j => (x j).val) (fun j => (q.1 j).val) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp only [Fin.append_left,Fin.append_right]
  change Fin.append (fun j => (x j).val) (Fin.append (fun j => (q.1 j).val) (fun j => (q.2 j).val)) ∘
    Fin.cast (Nat.add_assoc p n a) = Fin.append (fun j => ((Fin.append x q.1) j).val) (fun j => (q.2 j).val)
  rw [hv]
  exact (Fin.append_assoc _ _ _).symm

theorem mixedVFParameterDomain_row (U : Set (Point (M := M) (p+n) a))
    (x : Fin p → VF (M := M)) :
    {z : Fin (n+a) → M | Fin.append (fun j => (x j).val) z ∈ mixedVFParameterDomain U} =
      gammaPointCode '' vfParameterFibre U x := by
  ext z
  constructor
  · rintro ⟨hU,hproper⟩
    have hz : ∀ i, sortEval (gammaPointSort n a i) (z i) := by
      intro i
      simpa only [mixedVFParameterSort,Fin.append_right] using hproper (Fin.natAdd p i)
    let q := pointOfSortedCode z hz
    have hq : gammaPointCode q = z := pointOfSortedCode_code _ _
    refine ⟨q,?_,hq⟩
    rw [← hq,mixedVFParameterCode_append] at hU
    obtain ⟨u,hu,he⟩ := hU
    have he' : u = (Fin.append x q.1,q.2) := gammaPointCode_injective he
    change (Fin.append x q.1,q.2) ∈ U
    exact he' ▸ hu
  · rintro ⟨q,hq,rfl⟩
    refine ⟨?_,?_⟩
    · rw [mixedVFParameterCode_append]
      exact ⟨(Fin.append x q.1,q.2),hq,rfl⟩
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa only [mixedVFParameterSort,Fin.append_left,sortEval,iVF] using (x i).property
      · simpa only [mixedVFParameterSort,Fin.append_right] using gammaPointCode_proper q i

end IntegrationInACVF.Section6
