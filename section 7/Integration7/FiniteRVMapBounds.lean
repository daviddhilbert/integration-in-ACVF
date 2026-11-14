import Integration7.FiniteVolumeIsoCertificates
import IntegrationSection6.GammaFiniteTupleBounds
import Section9.SpecialJacobianGeneric

/-! Actual finite-fibre RV maps have uniform finite bounds over a small
real parameter set. Bounds follow from the checked tuple compactness theorem. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section8
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {a b : ℕ}

def rawRVMapReverseGraph
    {A : DefSet (rawRVSpace (M := M) a) S} {B : DefSet (rawRVSpace (M := M) b) S}
    (F : Map A B) : Set ((Fin b → M) × (Fin a → M)) :=
  {p | ∃ x : A, rvValues x.val = p.2 ∧ rvValues (F x).val = p.1}

theorem rawRVMapReverseGraph_definable
    {A : DefSet (rawRVSpace (M := M) a) S} {B : DefSet (rawRVSpace (M := M) b) S}
    (F : Map A B) : S.Definable LRV {w : Fin (b+a) → M |
      (w ∘ Fin.castAdd a,w ∘ Fin.natAdd b) ∈ rawRVMapReverseGraph F} := by
  let P := rawRVSpace (M := M) a
  let Q := rawRVSpace (M := M) b
  let j : Fin a ⊕ Fin b → Fin (b+a) := Sum.elim (Fin.natAdd b) (Fin.castAdd a)
  have h := F.graph_definable.preimage_comp j
  convert h using 1
  ext w
  constructor
  · rintro ⟨u,hx,hy⟩
    have hh : Sum.elim (rvValues u.val) (rvValues (F u).val) ∈ P.relation Q F.graph := by
      have hh := (P.relation_decode Q F.graph
        ⟨rvValues u.val,⟨u.val,rfl⟩⟩ ⟨rvValues (F u).val,⟨(F u).val,rfl⟩⟩).mpr
        (by simpa only [P,Q,decode_rvValues] using
          (show F.graph u.val (F u).val from ⟨u,rfl,rfl⟩))
      exact hh
    have he : Sum.elim (rvValues u.val) (rvValues (F u).val) = w ∘ j := by
      funext i
      cases i with
      | inl i => exact congrFun hx i
      | inr i => exact congrFun hy i
    change w ∘ j ∈ P.relation Q F.graph
    rw [← he]
    exact hh
  · rintro ⟨hx,hy,u,hux,huy⟩
    refine ⟨u,?_,?_⟩
    · exact (congrArg rvValues hux).trans (rvValues_decode ⟨_,hx⟩)
    · exact (congrArg rvValues huy).trans (rvValues_decode ⟨_,hy⟩)

theorem rawRVMapReverseGraph_finite
    {A : DefSet (rawRVSpace (M := M) a) S} {B : DefSet (rawRVSpace (M := M) b) S}
    (F : Map A B) (hF : F.FiniteFibres) (y : Fin b → M) :
    {x : Fin a → M | (y,x) ∈ rawRVMapReverseGraph F}.Finite := by
  by_cases h : ∃ v : B, rvValues v.val = y
  · obtain ⟨v,hv⟩ := h
    apply ((hF v).image (fun u : A => rvValues u.val)).subset
    rintro x ⟨u,hux,huy⟩
    have he : F u = v := Subtype.ext (rvValues_injective (huy.trans hv.symm))
    exact ⟨u,he,hux⟩
  · have he : {x : Fin a → M | (y,x) ∈ rawRVMapReverseGraph F} = ∅ := by
      ext x
      constructor
      · rintro ⟨u,_,hu⟩
        exact (h ⟨F u,hu⟩).elim
      · exact False.elim
    rw [he]
    exact Set.finite_empty

theorem finiteRVMap_uniform_bound
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hS : Cardinal.mk S < κ)
    {A : DefSet (rawRVSpace (M := M) a) S} {B : DefSet (rawRVSpace (M := M) b) S}
    (F : Map A B) (hF : F.FiniteFibres) :
    ∃ N : ℕ, ∀ y : Fin b → M, (∀ i, iRV (y i)) →
      {x : Fin a → M | (y,x) ∈ rawRVMapReverseGraph F}.ncard ≤ N := by
  let G : Base (M := M) := ⟨S,∅⟩
  let P : Set (Fin b → M) := sortedUniverse (fun _ => SortTag.rv)
  have hP : DefinableOverBase G (fun _ : Fin b => .rv) P :=
    real_definableOverBase G _ _ (sortedUniverse_definable S _)
  let R := rawRVMapReverseGraph F
  let T : Set (Fin (b+a) → M) := {w | (w ∘ Fin.castAdd a,w ∘ Fin.natAdd b) ∈ R}
  have hraw : @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) (Fin (b+a)) T :=
    Eq.mp (congrArg (fun I : LRV.Structure M => @Set.Definable M S LRV I (Fin (b+a)) T)
      (normalize_eq_of_isCanonical hc).symm) (rawRVMapReverseGraph_definable F)
  have hproper (w : Fin (b+a) → M) (hw : w ∈ T) :
      ∀ i, sortEval (Fin.append (fun _ : Fin b => SortTag.rv) (fun _ : Fin a => .rv) i) (w i) := by
    obtain ⟨u,hx,hy⟩ := hw
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have he : ((F u).val j).val = w (Fin.castAdd a j) := congrFun hy j
      have hv : iRV (w (Fin.castAdd a j)) := he ▸ ((F u).val j).property
      simpa only [Fin.append_left,sortEval,iRV] using hv
    · have he : (u.val j).val = w (Fin.natAdd b j) := congrFun hx j
      have hv : iRV (w (Fin.natAdd b j)) := he ▸ (u.val j).property
      simpa only [Fin.append_right,sortEval,iRV] using hv
  have hR : DefinableOverBase G (Fin.append (fun _ : Fin b => .rv) (fun _ : Fin a => .rv)) T :=
    real_definableOverBase G _ _ ((definableOver_iff_normalized_raw S _ T).mpr ⟨hraw,hproper⟩)
  have hγ : Cardinal.mk G.gamma < κ := by
    simpa only [G,Cardinal.mk_eq_zero_iff.mpr inferInstance] using (Cardinal.aleph0_pos.trans_le hκ)
  obtain ⟨N,hN⟩ := Section6.gamma_uniform_finite_tuple_rows hκ hs hS hγ _ _ P hP R hR
    (fun y _ => rawRVMapReverseGraph_finite F hF y)
  exact ⟨N,fun y hy => (hN y hy).2⟩

end IntegrationInACVF.Section7
