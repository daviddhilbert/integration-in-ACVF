module

public import Integration7.TypedVolumeDensityValidity
public import Integration7.NonzeroDensityFormulas
public import Section3.GammaBaseTools

@[expose] public section

/-! Adjoin a retained RV label as the density of any sorted family schema.
The nonzero guard is part of the formula; valid rows require precisely that
the retained label is nonzero throughout that row. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}
local notation "N" => (@CanonicalStructure.normalize M sM)

def sortedLabelEquality (st : Fin ((p+a)+1) → SortTag) (δ : Fin a) :
    Set (Fin ((p+a)+1) → M) :=
  {w | w ∈ sortedUniverse st ∧ w (Fin.last (p+a)) = w (Fin.castAdd 1 (Fin.natAdd p δ))}

theorem sortedLabelEquality_definable (st : Fin ((p+a)+1) → SortTag) (δ : Fin a) :
    DefinableOverBase B st (sortedLabelEquality (M := M) st δ) := by
  have hs := ((definableOver_iff_normalized_raw B.real st _).mp
    (sortedUniverse_definable B.real st)).1
  let S₀ : Set M := B.real
  have he : @Set.Definable M S₀ LRV N (Fin ((p+a)+1))
      {w | w (Fin.last (p+a)) = w (Fin.castAdd 1 (Fin.natAdd p δ))} := by
    letI : LRV.Structure M := N
    exact (Set.DefinableFun.proj (L := LRV) (A := S₀)).ofPred_eq
      (Set.DefinableFun.proj (L := LRV) (A := S₀))
  have hse : @Set.Definable M B.real LRV N (Fin ((p+a)+1))
      (sortedLabelEquality (M := M) st δ) := by
    letI : LRV.Structure M := N
    exact hs.inter he
  exact real_definableOverBase B st _
    ((definableOver_iff_normalized_raw B.real st _).mpr ⟨hse, fun _ h => h.1⟩)

def labelDensitySchema
    (F : GammaFiniteRVSchema B p a (k+1) sp) (δ : Fin a) : GammaRVVolumeSchema B p a k sp where
  object := F
  density := nonzeroDensityFormula
    ({w | w ∘ Fin.castAdd 1 ∈ F.domain ∧
      w ∈ sortedUniverse (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin 1 => .rv))} ∩
      sortedLabelEquality (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin 1 => .rv)) δ)
  density_definable := nonzeroDensityFormula_definable
    ((F.domain_definable.preimage_real _ (Fin.castAdd 1)).inter (sortedLabelEquality_definable _ δ))
  density_nonzero _ h := h.2

theorem labelDensitySchema_row
    (F : GammaFiniteRVSchema B p a (k+1) sp) (δ : Fin a)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (x : Fin a → CanonicalRV.RVSort M) (y : Fin 1 → CanonicalRV.RVSort M) :
    (labelDensitySchema F δ).rowDensity z x y ↔
      x ∈ F.rowDomain z ∧ y 0 = x δ ∧ (x δ).val ≠ iRVZero := by
  have hs : Fin.append (Fin.append z (rvValues x)) (rvValues y) ∈ sortedUniverse
      (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin 1 => .rv)) := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using hz i
      · simpa only [Fin.append_left, Fin.append_right, sortEval, iRV, rvValues] using (x i).property
    · simpa only [Fin.append_right, sortEval, iRV, rvValues] using (y i).property
  have hp : Fin.append (Fin.append z (rvValues x)) (rvValues y) ∘ Fin.castAdd 1 =
      Fin.append z (rvValues x) := funext (Fin.append_left _ _)
  change _ ∈ nonzeroDensityFormula _ ↔ _
  rw [nonzeroDensityFormula_append]
  change (((_ ∈ F.domain ∧ _) ∧ (_ ∧ _ = _)) ∧ _) ↔ _
  rw [hp]
  simp only [show Fin.last (p+a) = Fin.natAdd (p+a) (0 : Fin 1) from rfl,
    hs, and_true, true_and, Fin.append_right, Fin.append_left, rvValues]
  constructor
  · rintro ⟨⟨hx, he⟩, hn⟩
    exact ⟨hx, Subtype.ext he, fun h => hn (he.trans h)⟩
  · rintro ⟨hx, he, hn⟩
    exact ⟨⟨hx, congrArg Subtype.val he⟩, fun h => hn ((congrArg Subtype.val he).symm.trans h)⟩

theorem labelDensitySchema_valid
    (F : GammaFiniteRVSchema B p a (k+1) sp) (δ : Fin a)
    (z : Fin p → M) (hz : F.valid z)
    (hNZ : ∀ x : F.rowDomain z, (x.val δ).val ≠ iRVZero) : (labelDensitySchema F δ).valid z := by
  refine ⟨hz, ?_⟩
  apply (labelDensitySchema F δ).density_valid_of_typed z hz.1
  · intro x hx
    refine ⟨fun _ => x δ, ?_, ?_⟩
    · exact (labelDensitySchema_row F δ z hz.1 x _).mpr ⟨hx, rfl, hNZ ⟨x,hx⟩⟩
    · intro y hy
      have h := (labelDensitySchema_row F δ z hz.1 x y).mp hy
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact h.2.1
  · intro x y hy
    exact ((labelDensitySchema_row F δ z hz.1 x y).mp hy).1

end IntegrationInACVF.Section7
