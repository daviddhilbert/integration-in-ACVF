import IntegrationSection6.GammaSortedSchemaRows
import IntegrationSection6.GammaSchemaRowEquality

/-! Literal row agreement across different parameter arities and sorts.
This is the data relation used when VF parameter families descend to
prepared RV keys. It compares every raw source and volume tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def GammaSchemaRowAgreement (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M)
    (G : GammaFiniteRVSchema B q a k sq) (t : Fin q → M) : Prop :=
  (∀ x : Fin a → M, Fin.append z x ∈ F.domain ↔ Fin.append t x ∈ G.domain) ∧
  (∀ (x : Fin a → M) (y : Fin k → M),
    Fin.append (Fin.append z x) y ∈ F.volume ↔ Fin.append (Fin.append t x) y ∈ G.volume)

theorem GammaSchemaRowAgreement.symm
    {F : GammaFiniteRVSchema B p a k sp} {z : Fin p → M}
    {G : GammaFiniteRVSchema B q a k sq} {t : Fin q → M}
    (h : GammaSchemaRowAgreement F z G t) : GammaSchemaRowAgreement G t F z :=
  ⟨fun x => (h.1 x).symm,fun x y => (h.2 x y).symm⟩

theorem GammaSchemaRowAgreement.domains
    {F : GammaFiniteRVSchema B p a k sp} {z : Fin p → M}
    {G : GammaFiniteRVSchema B q a k sq} {t : Fin q → M}
    (h : GammaSchemaRowAgreement F z G t) : F.rowDomain z = G.rowDomain t :=
  Set.ext (fun x => h.1 (fun j => (x j).val))

theorem GammaSchemaRowAgreement.volumes
    {F : GammaFiniteRVSchema B p a k sp} {z : Fin p → M}
    {G : GammaFiniteRVSchema B q a k sq} {t : Fin q → M}
    (h : GammaSchemaRowAgreement F z G t) : F.rowVolume z = G.rowVolume t := by
  funext x y
  exact propext (h.2 (fun j => (x j).val) (fun j => (y j).val))

theorem gammaSchemaRowAgreement_of_typed (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M)
    (G : GammaFiniteRVSchema B q a k sq) (t : Fin q → M)
    (hD : ∀ x : Fin a → RV (M := M), x ∈ F.rowDomain z ↔ x ∈ G.rowDomain t)
    (hV : ∀ (x : Fin a → RV (M := M)) (y : Fin k → RV (M := M)), F.rowVolume z x y ↔ G.rowVolume t x y) :
    GammaSchemaRowAgreement F z G t := by
  constructor
  · intro x
    rw [F.raw_row_domain_iff,G.raw_row_domain_iff]
    exact exists_congr (fun u => and_congr (hD u) Iff.rfl)
  · intro x y
    rw [F.raw_row_volume_iff,G.raw_row_volume_iff]
    exact exists_congr (fun u => exists_congr (fun v => and_congr (hV u v) Iff.rfl))

theorem gammaSchemaSameRow_of_agreement
    {F H : GammaFiniteRVSchema B p a k sp} {G K : GammaFiniteRVSchema B q a k sq}
    {z : Fin p → M} {t : Fin q → M} (ht : ∀ j, sortEval (sq j) (t j))
    (hF : GammaSchemaRowAgreement F z G t) (hH : GammaSchemaRowAgreement H z K t)
    (h : F.sameRow H z) : G.sameRow K t :=
  ⟨ht,fun x => (hF.1 x).symm.trans ((h.2.1 x).trans (hH.1 x)),
    fun x y => (hF.2 x y).symm.trans ((h.2.2 x y).trans (hH.2 x y))⟩

end IntegrationInACVF.Section6
