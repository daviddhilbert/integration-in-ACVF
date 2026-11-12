import IntegrationSection6.GammaSortedSchemaRows

/-! Relational images of labels in sorted RV families. The construction
uses only original-base full Gamma formulas and real coordinate projections.
Functionality and finite volume fibres are certified at valid rows. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

def rawLabelImageDomainSource (p a b : ℕ) : Fin (p+a) → Fin ((p+b)+a) :=
  Fin.addCases (fun j => Fin.castAdd a (Fin.castAdd b j)) (Fin.natAdd (p+b))

def rawLabelImageDomainGraph (p a b : ℕ) : Fin (a+b) → Fin ((p+b)+a) :=
  Fin.addCases (Fin.natAdd (p+b)) (fun j => Fin.castAdd a (Fin.natAdd p j))

def rawLabelImageVolumeSource (p a b k : ℕ) : Fin ((p+a)+k) → Fin (((p+b)+k)+a) :=
  Fin.addCases
    (Fin.addCases (fun j => Fin.castAdd a (Fin.castAdd k (Fin.castAdd b j))) (Fin.natAdd ((p+b)+k)))
    (fun j => Fin.castAdd a (Fin.natAdd (p+b) j))

def rawLabelImageVolumeGraph (p a b k : ℕ) : Fin (a+b) → Fin (((p+b)+k)+a) :=
  Fin.addCases (Fin.natAdd ((p+b)+k)) (fun j => Fin.castAdd a (Fin.castAdd k (Fin.natAdd p j)))

def GammaFiniteRVSchema.labelImageDomain (F : GammaFiniteRVSchema B p a k sp)
    (H : Set (Fin (a+b) → M)) : Set (Fin (p+b) → M) :=
  {w | ∃ x : Fin a → M,
    (Fin.append w x ∘ rawLabelImageDomainSource p a b ∈ F.domain ∧
      Fin.append w x ∈ sortedUniverse (Fin.append (Fin.append sp (fun _ : Fin b => .rv)) (fun _ : Fin a => .rv))) ∧
    (Fin.append w x ∘ rawLabelImageDomainGraph p a b ∈ H ∧
      Fin.append w x ∈ sortedUniverse (Fin.append (Fin.append sp (fun _ : Fin b => .rv)) (fun _ : Fin a => .rv)))}

def GammaFiniteRVSchema.labelImageVolume (F : GammaFiniteRVSchema B p a k sp)
    (H : Set (Fin (a+b) → M)) : Set (Fin ((p+b)+k) → M) :=
  {w | ∃ x : Fin a → M,
    (Fin.append w x ∘ rawLabelImageVolumeSource p a b k ∈ F.volume ∧
      Fin.append w x ∈ sortedUniverse (Fin.append (Fin.append (Fin.append sp (fun _ : Fin b => .rv)) (fun _ : Fin k => .rv)) (fun _ : Fin a => .rv))) ∧
    (Fin.append w x ∘ rawLabelImageVolumeGraph p a b k ∈ H ∧
      Fin.append w x ∈ sortedUniverse (Fin.append (Fin.append (Fin.append sp (fun _ : Fin b => .rv)) (fun _ : Fin k => .rv)) (fun _ : Fin a => .rv)))}

theorem GammaFiniteRVSchema.labelImageDomain_definable (F : GammaFiniteRVSchema B p a k sp)
    {H : Set (Fin (a+b) → M)} (hH : DefinableOverBase B (fun _ => .rv) H) :
    DefinableOverBase B (Fin.append sp (fun _ : Fin b => .rv)) (F.labelImageDomain H) :=
  gamma_family_row_exists_definable _ _
    ((F.domain_definable.preimage_real _ (rawLabelImageDomainSource p a b)).inter
      (hH.preimage_real _ (rawLabelImageDomainGraph p a b)))

theorem GammaFiniteRVSchema.labelImageVolume_definable (F : GammaFiniteRVSchema B p a k sp)
    {H : Set (Fin (a+b) → M)} (hH : DefinableOverBase B (fun _ => .rv) H) :
    DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin b => .rv)) (fun _ : Fin k => .rv))
      (F.labelImageVolume H) :=
  gamma_family_row_exists_definable _ _
    ((F.volume_definable.preimage_real _ (rawLabelImageVolumeSource p a b k)).inter
      (hH.preimage_real _ (rawLabelImageVolumeGraph p a b k)))

def GammaFiniteRVSchema.labelImageFormula (F : GammaFiniteRVSchema B p a k sp)
    {H : Set (Fin (a+b) → M)} (hH : DefinableOverBase B (fun _ => .rv) H) :
    GammaFiniteRVSchema B p b k sp :=
  ⟨F.labelImageDomain H,F.labelImageVolume H,F.labelImageDomain_definable hH,F.labelImageVolume_definable hH,0⟩

def GammaFiniteRVSchema.unionFormula (F G : GammaFiniteRVSchema B p a k sp) :
    GammaFiniteRVSchema B p a k sp :=
  ⟨F.domain ∪ G.domain,F.volume ∪ G.volume,
    F.domain_definable.union G.domain_definable,F.volume_definable.union G.volume_definable,0⟩

end IntegrationInACVF.Section6
