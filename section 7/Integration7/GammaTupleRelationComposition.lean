import Integration7.GammaVolumeSchemaRestrictions

/-! Composition of original-base RV relation formulas with a shared
sorted parameter block. The intermediate labels remain quantified variables. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b c : ℕ}

def familyRelationCompose (H : Set (Fin ((p+a)+b) → M)) (K : Set (Fin ((p+b)+c) → M)) :
    Set (Fin ((p+a)+c) → M) :=
  {w | ∃ y : Fin b → M,
    Fin.append (w ∘ Fin.castAdd c) y ∈ H ∧
    Fin.append (Fin.append (w ∘ Fin.castAdd c ∘ Fin.castAdd a) y)
      (w ∘ Fin.natAdd (p+a)) ∈ K}

theorem familyRelationCompose_definable (sp : Fin p → SortTag)
    {H : Set (Fin ((p+a)+b) → M)} {K : Set (Fin ((p+b)+c) → M)}
    (hH : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) H)
    (hK : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin b => .rv)) (fun _ : Fin c => .rv)) K) :
    DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin c => .rv))
      (familyRelationCompose H K) := by
  let L := (p+a)+c
  let st := Fin.append (Fin.append (Fin.append sp (fun _ : Fin a => SortTag.rv))
    (fun _ : Fin c => .rv)) (fun _ : Fin b => .rv)
  let iH : Fin ((p+a)+b) → Fin (L+b) :=
    Fin.addCases (fun j => Fin.castAdd b (Fin.castAdd c j)) (Fin.natAdd L)
  let iK : Fin ((p+b)+c) → Fin (L+b) :=
    Fin.addCases
      (Fin.addCases (fun j => Fin.castAdd b (Fin.castAdd c (Fin.castAdd a j))) (Fin.natAdd L))
      (fun j => Fin.castAdd b (Fin.natAdd (p+a) j))
  have sH (w : Fin L → M) (y : Fin b → M) :
      Fin.append w y ∘ iH = Fin.append (w ∘ Fin.castAdd c) y := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      simp only [iH,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,
        Fin.append_left,Fin.append_right]
  have sK (w : Fin L → M) (y : Fin b → M) :
      Fin.append w y ∘ iK = Fin.append (Fin.append (w ∘ Fin.castAdd c ∘ Fin.castAdd a) y)
        (w ∘ Fin.natAdd (p+a)) := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp only [iK,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,
          Fin.append_left,Fin.append_right]
    · simp only [iK,Function.comp_apply,Fin.addCases_right,Fin.append_left,Fin.append_right]
  have h := gamma_family_row_exists_definable _ _
    ((hH.preimage_real st iH).inter (hK.preimage_real st iK))
  convert h using 1
  ext w
  apply exists_congr
  intro y
  change (_ ∧ _) ↔ ((_ ∧ _) ∧ (_ ∧ _))
  rw [sH,sK]
  constructor
  · rintro ⟨h₁,h₂⟩
    have hs : Fin.append w y ∈ sortedUniverse st := by
      intro j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simpa only [st,Fin.append_left,Function.comp_apply] using
            hH.proper _ h₁ (Fin.castAdd b j)
        · simpa only [st,Fin.append_left,Fin.append_right,Function.comp_apply] using
            hK.proper _ h₂ (Fin.natAdd (p+b) j)
      · simpa only [st,Fin.append_right] using hH.proper _ h₁ (Fin.natAdd (p+a) j)
    exact ⟨⟨h₁,hs⟩,h₂,hs⟩
  · rintro ⟨⟨h₁,_⟩,h₂,_⟩
    exact ⟨h₁,h₂⟩

private theorem appendLeftComposition {X : Type} {u v : ℕ} (x : Fin u → X) (y : Fin v → X) :
    Fin.append x y ∘ Fin.castAdd v = x := funext (Fin.append_left _ _)
private theorem appendRightComposition {X : Type} {u v : ℕ} (x : Fin u → X) (y : Fin v → X) :
    Fin.append x y ∘ Fin.natAdd u = y := funext (Fin.append_right _ _)

theorem familyRelationCompose_append
    (H : Set (Fin ((p+a)+b) → M)) (K : Set (Fin ((p+b)+c) → M))
    (z : Fin p → M) (x : Fin a → M) (v : Fin c → M) :
    Fin.append (Fin.append z x) v ∈ familyRelationCompose H K ↔
      ∃ y : Fin b → M, Fin.append (Fin.append z x) y ∈ H ∧ Fin.append (Fin.append z y) v ∈ K := by
  change (∃ y : Fin b → M, _ ∧ _) ↔ _
  have hp : Fin.append (Fin.append z x) v ∘ Fin.castAdd c ∘ Fin.castAdd a = z := by
    funext q
    simp only [Function.comp_apply,Fin.append_left]
  rw [hp,appendLeftComposition,appendRightComposition]

end IntegrationInACVF.Section7
