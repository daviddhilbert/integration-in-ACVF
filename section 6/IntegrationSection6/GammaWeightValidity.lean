import IntegrationSection6.RawWeightDefinability
import IntegrationSection6.GammaFamilyValidity

/-! First-order weight validity of a chart and its two volume graphs.
The parameter block is fixed and all four RV blocks are quantified with
proper-sort guards. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section7
namespace IntegrationInACVF.Section6

def chartRowX {Y : Type*} (a b k : ℕ) (r : Fin ((a+b)+(k+k)) → Y) : Fin a → Y :=
  fun j => r (Fin.castAdd (k+k) (Fin.castAdd b j))
def chartRowY {Y : Type*} (a b k : ℕ) (r : Fin ((a+b)+(k+k)) → Y) : Fin b → Y :=
  fun j => r (Fin.castAdd (k+k) (Fin.natAdd a j))
def chartRowU {Y : Type*} (a b k : ℕ) (r : Fin ((a+b)+(k+k)) → Y) : Fin k → Y :=
  fun j => r (Fin.natAdd (a+b) (Fin.castAdd k j))
def chartRowV {Y : Type*} (a b k : ℕ) (r : Fin ((a+b)+(k+k)) → Y) : Fin k → Y :=
  fun j => r (Fin.natAdd (a+b) (Fin.natAdd k j))

def tripleTupleCoordinates {p a b q : ℕ} (ip : Fin p → Fin q) (ix : Fin a → Fin q)
    (iy : Fin b → Fin q) : Fin ((p+a)+b) → Fin q := Fin.addCases (Fin.addCases ip ix) iy

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ}

def weightedChartRowValid (sp : Fin p → SortTag)
    (H : Set (Fin ((p+a)+b) → M)) (F : Set (Fin ((p+a)+k) → M))
    (G : Set (Fin ((p+b)+k) → M)) (z : Fin p → M) : Prop :=
  (∀ i, sortEval (sp i) (z i)) ∧
  ∀ r : Fin ((a+b)+(k+k)) → M, (∀ j, iRV (r j)) →
    Fin.append (Fin.append z (chartRowX a b k r)) (chartRowY a b k r) ∈ H →
    Fin.append (Fin.append z (chartRowX a b k r)) (chartRowU a b k r) ∈ F →
    Fin.append (Fin.append z (chartRowY a b k r)) (chartRowV a b k r) ∈ G →
    rawWeight (chartRowU a b k r) = rawWeight (chartRowV a b k r)

theorem gamma_weighted_chart_validity_definable (sp : Fin p → SortTag)
    {H : Set (Fin ((p+a)+b) → M)} {F : Set (Fin ((p+a)+k) → M)} {G : Set (Fin ((p+b)+k) → M)}
    (hH : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) H)
    (hF : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin k => .rv)) F)
    (hG : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin b => .rv)) (fun _ : Fin k => .rv)) G) :
    DefinableOverBase B sp {z | weightedChartRowValid sp H F G z} := by
  let q := (a+b)+(k+k)
  let st := Fin.append sp (fun _ : Fin q => SortTag.rv)
  let ip : Fin p → Fin (p+q) := Fin.castAdd q
  let ix : Fin a → Fin (p+q) := fun j => Fin.natAdd p (Fin.castAdd (k+k) (Fin.castAdd b j))
  let iy : Fin b → Fin (p+q) := fun j => Fin.natAdd p (Fin.castAdd (k+k) (Fin.natAdd a j))
  let iu : Fin k → Fin (p+q) := fun j => Fin.natAdd p (Fin.natAdd (a+b) (Fin.castAdd k j))
  let iv : Fin k → Fin (p+q) := fun j => Fin.natAdd p (Fin.natAdd (a+b) (Fin.natAdd k j))
  let cH := tripleTupleCoordinates ip ix iy
  let cF := tripleTupleCoordinates ip ix iu
  let cG := tripleTupleCoordinates ip iy iv
  let cW : Fin (k+k) → Fin (p+q) := fun j => Fin.natAdd p (Fin.natAdd (a+b) j)
  have sH (z : Fin p → M) (r : Fin q → M) :
      Fin.append z r ∘ cH = Fin.append (Fin.append z (chartRowX a b k r)) (chartRowY a b k r) := by
    funext j
    refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) l <;>
        simp only [cH,tripleTupleCoordinates,ip,ix,Function.comp_apply,Fin.addCases_left,Fin.append_left,Fin.append_right,Fin.addCases_right,chartRowX]
    · simp only [cH,tripleTupleCoordinates,iy,Function.comp_apply,Fin.addCases_right,Fin.append_right,chartRowY]
  have sF (z : Fin p → M) (r : Fin q → M) :
      Fin.append z r ∘ cF = Fin.append (Fin.append z (chartRowX a b k r)) (chartRowU a b k r) := by
    funext j
    refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) l <;>
        simp only [cF,tripleTupleCoordinates,ip,ix,Function.comp_apply,Fin.addCases_left,Fin.append_left,Fin.append_right,Fin.addCases_right,chartRowX]
    · simp only [cF,tripleTupleCoordinates,iu,Function.comp_apply,Fin.addCases_right,Fin.append_right,chartRowU]
  have sG (z : Fin p → M) (r : Fin q → M) :
      Fin.append z r ∘ cG = Fin.append (Fin.append z (chartRowY a b k r)) (chartRowV a b k r) := by
    funext j
    refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) l <;>
        simp only [cG,tripleTupleCoordinates,ip,iy,Function.comp_apply,Fin.addCases_left,Fin.append_left,Fin.append_right,Fin.addCases_right,chartRowY]
    · simp only [cG,tripleTupleCoordinates,iv,Function.comp_apply,Fin.addCases_right,Fin.append_right,chartRowV]
  have sW (z : Fin p → M) (r : Fin q → M) :
      Fin.append z r ∘ cW = Fin.append (chartRowU a b k r) (chartRowV a b k r) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp only [cW,Function.comp_apply,Fin.append_right,Fin.append_left,chartRowU,chartRowV]
  let A : Set (Fin (p+q) → M) :=
    {w | ((w ∘ cH ∈ H ∧ w ∈ sortedUniverse st) ∧ (w ∘ cF ∈ F ∧ w ∈ sortedUniverse st)) ∧
      (w ∘ cG ∈ G ∧ w ∈ sortedUniverse st)}
  have hA : DefinableOverBase B st A :=
    ((hH.preimage_real st cH).inter (hF.preimage_real st cF)).inter (hG.preimage_real st cG)
  let W : Set (Fin (k+k) → M) := {t | (∀ j, iRV (t j)) ∧
    rawWeight (t ∘ Fin.castAdd k) = rawWeight (t ∘ Fin.natAdd k)}
  have hW : DefinableOverBase B (fun _ : Fin (k+k) => .rv) W :=
    real_definableOverBase B _ _ (rawWeight_balance_definable B.real k)
  let C : Set (Fin (p+q) → M) := {w | w ∘ cW ∈ W ∧ w ∈ sortedUniverse st}
  have hC : DefinableOverBase B st C := hW.preimage_real st cW
  have h := gamma_family_row_subset_definable sp (fun _ : Fin q => .rv) hA hC
  convert h using 1
  apply Set.ext
  intro z
  constructor
  · rintro ⟨hz,hvalid⟩
    refine ⟨hz,?_⟩
    intro r hr
    have hsort : Fin.append z r ∈ sortedUniverse st := hr.1.1.2
    have hrRV : ∀ j, iRV (r j) := by
      intro j
      simpa only [st,Fin.append_right,sortEval,iRV] using hsort (Fin.natAdd p j)
    have hh : Fin.append (Fin.append z (chartRowX a b k r)) (chartRowY a b k r) ∈ H := (sH z r) ▸ hr.1.1.1
    have hf : Fin.append (Fin.append z (chartRowX a b k r)) (chartRowU a b k r) ∈ F := (sF z r) ▸ hr.1.2.1
    have hg : Fin.append (Fin.append z (chartRowY a b k r)) (chartRowV a b k r) ∈ G := (sG z r) ▸ hr.2.1
    refine ⟨?_,hsort⟩
    change ((∀ j, iRV ((Fin.append z r ∘ cW) j)) ∧ _)
    rw [sW]
    constructor
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa only [Fin.append_left,chartRowU] using hrRV (Fin.natAdd (a+b) (Fin.castAdd k i))
      · simpa only [Fin.append_right,chartRowV] using hrRV (Fin.natAdd (a+b) (Fin.natAdd k i))
    · simpa only [Function.comp_def,Fin.append_left,Fin.append_right] using hvalid r hrRV hh hf hg
  · rintro ⟨hz,hvalid⟩
    refine ⟨hz,?_⟩
    intro r hrRV hh hf hg
    have hsort : Fin.append z r ∈ sortedUniverse st := by
      intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · have hs : st (Fin.castAdd q i) = sp i := Fin.append_left sp (fun _ : Fin q => SortTag.rv) i
        have hz' : sortEval (st (Fin.castAdd q i)) (z i) := hs.symm ▸ hz i
        exact (Fin.append_left z r i).symm ▸ hz'
      · simpa only [st,Fin.append_right,sortEval,iRV] using hrRV i
    have hArow : Fin.append z r ∈ A :=
      ⟨⟨⟨(sH z r).symm ▸ hh,hsort⟩,⟨(sF z r).symm ▸ hf,hsort⟩⟩,⟨(sG z r).symm ▸ hg,hsort⟩⟩
    have hc := (hvalid r hArow).1.2
    change rawWeight ((Fin.append z r ∘ cW) ∘ Fin.castAdd k) =
      rawWeight ((Fin.append z r ∘ cW) ∘ Fin.natAdd k) at hc
    rw [sW] at hc
    simpa only [Function.comp_def,Fin.append_left,Fin.append_right] using hc

end IntegrationInACVF.Section6
