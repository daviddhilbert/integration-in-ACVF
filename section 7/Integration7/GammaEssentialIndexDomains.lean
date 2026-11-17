module

public import Integration7.GammaEssentialVolumeGraphs
public import IntegrationSection6.GammaGraphPresentationRestriction

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual original-Gamma subdomain of an index presentation where
every base volume coordinate is nonzero, including base degree zero. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p d : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

def essentialIndexDomain (BP : GammaFiniteGraphPresentation B p d T R) :
    Set (Fin p → RV (M := M)) := {t | t ∈ T ∧ ∀ i, (BP.totalVolume t i).val ≠ iRVZero}

theorem essential_index_domain_gamma
    (BP : GammaFiniteGraphPresentation B p d T R) :
    GammaSetDefinable B {t : Point (M := M) 0 p | t.2 ∈ (essentialIndexDomain BP)} := by
  have hNZ : GammaSetDefinable B {q : Point (M := M) 0 d | ∀ i, (q.2 i).val ≠ iRVZero} := by
    have h := gamma_rv_set_from_tuple_formula (nonzeroRVTuples_definable B d)
    convert h using 1
    ext q
    change (∀ i, (q.2 i).val ≠ iRVZero) ↔ Proper (rvValues q.2)
    exact ⟨fun h i => ⟨(q.2 i).property,h i⟩,fun h i => (h i).2⟩
  have h := (gammaLogicInput B).image_graph
    ((gammaLogicInput B).restrict_graph hNZ ((gammaLogicInput B).swap_graph BP.totalVolume_definable))
  convert h using 1
  ext t
  constructor
  · rintro ⟨ht,hNZt⟩
    exact ⟨(Fin.elim0,BP.totalVolume t.2),hNZt,ht,rfl⟩
  · rintro ⟨q,hNZq,ht,heq⟩
    exact ⟨ht,fun i => (congrArg (fun v => (v i).val) heq) ▸ hNZq i⟩

def essentialIndexPresentation (BP : GammaFiniteGraphPresentation B p d T R) :
    GammaFiniteGraphPresentation B p d (essentialIndexDomain BP)
      (fun x y => x ∈ (essentialIndexDomain BP) ∧ BP.totalVolume x = y) :=
  BP.restrictDomain (essentialIndexDomain BP) (fun _ h => h.1) (essential_index_domain_gamma BP)

theorem essential_index_presentation_volume
    (BP : GammaFiniteGraphPresentation B p d T R)
    (t : Fin p → RV (M := M)) (ht : t ∈ (essentialIndexDomain BP)) :
    (essentialIndexPresentation BP).totalVolume t = BP.totalVolume t :=
  BP.restrictDomain_totalVolume (essentialIndexDomain BP) (fun _ h => h.1) (essential_index_domain_gamma BP) t ht

end IntegrationInACVF.Section7
