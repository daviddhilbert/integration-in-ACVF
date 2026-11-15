import IntegrationSection4.GammaRVMapOperations

/-! Selecting whole fibres of a Gamma RV map preserves its actual
graphs and its original parameter fibres. No real representatives of
the selected RV parameters are named. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section4.GammaRVMap
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {n m d : ℕ} {A : Set (Point (M := M) n m)}

def selectedDomain (P : GammaRVMap G A d) (R : Set (Point (M := M) 0 d)) : Set (Point (M := M) n m) :=
  {p | ∃ a : A, a.val = p ∧ (Fin.elim0,P.toFun a) ∈ R}

def selectedInclusion (P : GammaRVMap G A d) (R : Set (Point (M := M) 0 d))
    (a : P.selectedDomain R) : A :=
  ⟨a.val,by obtain ⟨b,hb,_⟩ := a.property; exact hb ▸ b.property⟩

theorem selected_inclusion_value (P : GammaRVMap G A d) (R : Set (Point (M := M) 0 d))
    (a : P.selectedDomain R) : (P.selectedInclusion R a).val = a.val := rfl

theorem selected_inclusion_parameter (P : GammaRVMap G A d) (R : Set (Point (M := M) 0 d))
    (a : P.selectedDomain R) : (Fin.elim0,P.toFun (P.selectedInclusion R a)) ∈ R := by
  obtain ⟨b,hb,hR⟩ := a.property
  have he : b = P.selectedInclusion R a := Subtype.ext hb
  exact (congrArg (fun x => (Fin.elim0,P.toFun x) ∈ R) he).mp hR

theorem selected_domain_gamma (P : GammaRVMap G A d) {R : Set (Point (M := M) 0 d)}
    (hR : GammaSetDefinable G R) : GammaSetDefinable G (P.selectedDomain R) := by
  have h := (gammaLogicInput G).image_graph
    ((gammaLogicInput G).restrict_graph hR ((gammaLogicInput G).swap_graph P.graph))
  convert h using 1
  ext p
  constructor
  · rintro ⟨a,ha,hR⟩
    exact ⟨(Fin.elim0,P.toFun a),hR,a,ha,rfl⟩
  · rintro ⟨q,hq,a,ha,hPa⟩
    have he : (Fin.elim0,P.toFun a) = q := Prod.ext (by funext i; exact i.elim0) hPa
    exact ⟨a,ha,he.symm ▸ hq⟩

theorem selected_inclusion_graph (P : GammaRVMap G A d) {R : Set (Point (M := M) 0 d)}
    (hR : GammaSetDefinable G R) :
    GammaGraphDefinable G (fun (p q : Point (M := M) n m) =>
      ∃ a : P.selectedDomain R, a.val = p ∧ (P.selectedInclusion R a).val = q) := by
  let U := PresentedSet.univ (pointSpace (M := M) n m) G.real
  have h := (gammaLogicInput G).restrict_graph (P.selected_domain_gamma hR)
    ((gammaLogicInput G).real_map_graph (Map.id U))
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨hp,b,hb,hq⟩
    exact ⟨⟨p,hp⟩,rfl,hb.symm.trans hq⟩
  · rintro ⟨a,rfl,ha⟩
    exact ⟨a.property,⟨a.val,Set.mem_univ _⟩,rfl,ha⟩

def select (P : GammaRVMap G A d) {R : Set (Point (M := M) 0 d)} (hR : GammaSetDefinable G R) :
    GammaRVMap G (P.selectedDomain R) d :=
  P.precomp (P.selectedInclusion R) (P.selected_inclusion_graph hR)

theorem selected_parameter_fibre (P : GammaRVMap G A d) {R : Set (Point (M := M) 0 d)}
    (hR : GammaSetDefinable G R) (a₀ : P.selectedDomain R) :
    {p | ∃ a : P.selectedDomain R, a.val = p ∧ (P.select hR).toFun a = (P.select hR).toFun a₀} =
      {p | ∃ a : A, a.val = p ∧ P.toFun a = P.toFun (P.selectedInclusion R a₀)} := by
  ext p
  constructor
  · rintro ⟨a,ha,he⟩
    exact ⟨P.selectedInclusion R a,ha,he⟩
  · rintro ⟨a,ha,he⟩
    have hSel : (Fin.elim0,P.toFun a) ∈ R :=
      (congrArg (fun r => (Fin.elim0,r) ∈ R) he).mpr (P.selected_inclusion_parameter R a₀)
    let b : P.selectedDomain R := ⟨a.val,a,rfl,hSel⟩
    have hb : P.selectedInclusion R b = a := Subtype.ext rfl
    exact ⟨b,ha,(congrArg P.toFun hb).trans he⟩

end IntegrationInACVF.Section4.GammaRVMap
