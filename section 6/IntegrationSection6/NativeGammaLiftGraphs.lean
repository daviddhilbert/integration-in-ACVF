import IntegrationSection6.NormalizedLiftDomains
import Section7.GammaLiftEquivalence

/-! Full Gamma graphs of native VF lifting relations. This retains the
sorted interpretation instead of imposing canonical totalization on the
original one-sorted model. The coordinate proof adapts the checked
Section7/GammaLiftEquivalence.lean at revision
9cc9760892092dd34cfad4a6dee655843c52f30c (MIT per Lake metadata). -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}
variable {U V : GammaRVObject B k}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem nativeVFPairGraph_definable
    (A : Set (Fin (k + k) → M)) (hA : @Set.Definable M B.real LRV N (Fin (k+k)) A) (m l : ℕ) :
    GammaGraphDefinable B (fun (p : Point (M := M) k m) (q : Point (M := M) k l) =>
      productTuple (fun i => (p.1 i).val) (fun i => (q.1 i).val) ∈ A) := by
  let σ := Fin.append (gammaPointSort k m) (gammaPointSort k l)
  let π : Fin (k + k) → Fin ((k + m) + (k + l)) :=
    Fin.addCases (fun i => Fin.castAdd (k + l) (Fin.castAdd m i))
      (fun i => Fin.natAdd (k + m) (Fin.castAdd l i))
  let Z : Set (Fin ((k + m) + (k + l)) → M) :=
    {z | z ∘ π ∈ A ∧ ∀ i, sortEval (σ i) (z i)}
  have hSort : @Set.Definable M B.real LRV N (Fin ((k+m)+(k+l))) (sortedUniverse σ) :=
    ((definableOver_iff_normalized_raw B.real σ (sortedUniverse σ)).mp (sortedUniverse_definable B.real σ)).1
  have hZ : @Set.Definable M B.real LRV N (Fin ((k+m)+(k+l))) Z := by
    letI : LRV.Structure M := N
    exact (hA.preimage_comp π).inter hSort
  have hZ' := real_definableOverBase B σ Z
    ((definableOver_iff_normalized_raw B.real σ Z).mpr ⟨hZ,fun _ hz => hz.2⟩)
  unfold GammaGraphDefinable
  convert hZ' using 1
  have hcode (p : Point (M := M) k m) (q : Point (M := M) k l) :
      Fin.append (gammaPointCode p) (gammaPointCode q) ∘ π =
        productTuple (fun i => (p.1 i).val) (fun i => (q.1 i).val) := by
    apply productTuple_ext
    · intro i
      rw [productTuple_left]
      change Fin.append (gammaPointCode p) (gammaPointCode q) (π (Fin.castAdd k i)) = _
      simp only [π, Fin.addCases_left, Fin.append_left, gammaPointCode, vfAt]
    · intro i
      rw [productTuple_right]
      change Fin.append (gammaPointCode p) (gammaPointCode q) (π (Fin.natAdd k i)) = _
      simp only [π, Fin.addCases_right, Fin.append_right, gammaPointCode, Fin.append_left, vfAt]
  have hsort {r : ℕ} (p : Point (M := M) k r) (i : Fin (k + r)) :
      sortEval (gammaPointSort k r i) (gammaPointCode p i) := by
    cases i using Fin.addCases with
    | left i => simpa only [gammaPointSort, gammaPointCode, Fin.append_left, vfAt, sortEval, iVF]
        using (p.1 i).property
    | right i => simpa only [gammaPointSort, gammaPointCode, Fin.append_right, sortEval, iRV]
        using (p.2 i).property
  ext z
  constructor
  · rintro ⟨p, q, h, rfl⟩
    refine ⟨(hcode p q).symm ▸ h, ?_⟩
    intro i
    cases i using Fin.addCases with
    | left i => simpa only [σ, Fin.append_left] using hsort p i
    | right i => simpa only [σ, Fin.append_right] using hsort q i
  · intro hz
    let a (i : Fin (k + m)) := z (Fin.castAdd (k + l) i)
    let b (i : Fin (k + l)) := z (Fin.natAdd (k + m) i)
    have ha (i) : sortEval (gammaPointSort k m i) (a i) := by
      simpa only [a, σ, Fin.append_left] using hz.2 (Fin.castAdd (k + l) i)
    have hb (i) : sortEval (gammaPointSort k l i) (b i) := by
      simpa only [b, σ, Fin.append_right] using hz.2 (Fin.natAdd (k + m) i)
    let p : Point (M := M) k m :=
      (fun i => ⟨a (Fin.castAdd m i), by simpa only [gammaPointSort, Fin.append_left, sortEval, iVF] using ha (Fin.castAdd m i)⟩,
        fun i => ⟨a (Fin.natAdd k i), by simpa only [gammaPointSort, Fin.append_right, sortEval, iRV] using ha (Fin.natAdd k i)⟩)
    let q : Point (M := M) k l :=
      (fun i => ⟨b (Fin.castAdd l i), by simpa only [gammaPointSort, Fin.append_left, sortEval, iVF] using hb (Fin.castAdd l i)⟩,
        fun i => ⟨b (Fin.natAdd k i), by simpa only [gammaPointSort, Fin.append_right, sortEval, iRV] using hb (Fin.natAdd k i)⟩)
    have hp : gammaPointCode p = a := by
      funext i
      cases i using Fin.addCases <;> simp [gammaPointCode, vfAt, p]
    have hq : gammaPointCode q = b := by
      funext i
      cases i using Fin.addCases <;> simp [gammaPointCode, vfAt, q]
    have he : Fin.append (gammaPointCode p) (gammaPointCode q) = z := by
      rw [hp, hq]
      funext i
      cases i using Fin.addCases <;> simp [a, b]
    refine ⟨p, q, ?_, he⟩
    change productTuple (fun i => (p.1 i).val) (fun i => (q.1 i).val) ∈ A
    rw [← hcode p q, he]
    exact hz.1

theorem nativeGammaLiftGraph_definable
    (e : GammaRVIso U V) (A : Set (Fin (k + k) → M)) (hA : @Set.Definable M B.real LRV N (Fin (k+k)) A) :
    GammaGraphDefinable B (gammaLiftGraph e.equiv A) := by
  let m := rvObjectArity U.object
  let l := rvObjectArity V.object
  let L := gammaLogicInput B
  have h := e.graph.preimage_maps (pointLabels B.real k m) (pointLabels B.real k l)
  have hp := L.restrict_graph U.lift_definable h
  have hq := L.swap_graph (L.restrict_graph V.lift_definable (L.swap_graph hp))
  have hR := hq.inter (nativeVFPairGraph_definable A hA m l)
  apply GammaGraphDefinable.congr hR
  intro p q
  unfold gammaLiftGraph gammaRVLabelGraph
  rw [pointLabels_snd, pointLabels_snd]
  tauto


end IntegrationInACVF.Section6
