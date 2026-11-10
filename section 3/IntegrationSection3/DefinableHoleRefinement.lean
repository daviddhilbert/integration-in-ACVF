module

public import IntegrationSection3.PunctureFormulas
public import IntegrationSection3.PunctureCuts
public import IntegrationSection3.AtomicRegions

@[expose] public section

/-! Definable finite additions to the canonical holes of disjoint positive
regions. Finiteness and properness of a proposed geometric construction are
explicit inputs. The atomicity contradiction is proved here; the actual
fixed-radius and affine constructions must supply those inputs separately. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters
open IntegrationInACVF.Section3.PuncturedDecomposition
open IntegrationInACVF.Section3.MinimalBallSupport

namespace IntegrationInACVF.Section3.DefinableHoleRefinement

variable {X J : Type*}

def original (F : Finset (Set X)) (U : J → Set X) (h p : J) : Prop := U h ∈ holes F (U p)

def enlarged (F : Finset (Set X)) (U : J → Set X) (E : J → J → J → Prop) (k p : J) : Prop :=
  original F U k p ∨ PunctureFormulas.transported (original F U) E k p

def body (F : Finset (Set X)) (U : J → Set X) (E : J → J → J → Prop) : J → Set X :=
  PunctureFormulas.puncturedFamily (enlarged F U E) U

theorem names_finite {F : Finset (Set X)} {U : J → Set X} (hinj : Function.Injective U)
    {E : J → J → J → Prop}
    (hEfin : ∀ p, {k | PunctureFormulas.transported (original F U) E k p}.Finite) (p : J) :
    {k | enlarged F U E k p}.Finite := by
  have hOld : {k | original F U k p}.Finite :=
    (holes F (U p)).finite_toSet.preimage hinj.injOn
  exact hOld.union (hEfin p)

theorem enlarged_proper {F : Finset (Set X)} {U : J → Set X} {E : J → J → J → Prop}
    (hproper : ∀ h p k, original F U h p → E h p k → U k ⊂ U p)
    {k p : J} (hk : enlarged F U E k p) : U k ⊂ U p := by
  rcases hk with hold | ⟨h,hh,he⟩
  · exact (mem_holes.mp hold).2.1
  · exact hproper h p k hh he

theorem body_nonempty {balls : Set (Set X)} (hnf : AvoidsFiniteProperSubballs balls)
    {F : Finset (Set X)} {U : J → Set X} (hinj : Function.Injective U)
    (hU : ∀ j, U j ∈ balls) {E : J → J → J → Prop}
    (hEfin : ∀ p, {k | PunctureFormulas.transported (original F U) E k p}.Finite)
    (hproper : ∀ h p k, original F U h p → E h p k → U k ⊂ U p) (p : J) :
    (body F U E p).Nonempty := by
  classical
  have hf := (names_finite hinj hEfin p).image U
  let G := hf.toFinset
  have hG : ∀ b ∈ G, b ∈ balls ∧ b ⊂ U p := by
    intro b hb
    obtain ⟨k,hk,he⟩ := hf.mem_toFinset.mp hb
    rw [← he]
    exact ⟨hU k,enlarged_proper hproper hk⟩
  obtain ⟨x,hx,havoid⟩ := hnf (U p) (hU p) G hG
  refine ⟨x,hx,?_⟩
  rintro ⟨k,hk,hxk⟩
  exact havoid (U k) (hf.mem_toFinset.mpr ⟨k,hk,rfl⟩) hxk

theorem body_subset_region {F : Finset (Set X)} {U : J → Set X}
    (hcodes : ∀ b ∈ F, ∃ j, U j = b) (E : J → J → J → Prop) (p : J) :
    body F U E p ⊆ region F (U p) := by
  rintro x ⟨hx,hn⟩
  rw [region_eq_sdiff_holes]
  refine ⟨hx,?_⟩
  rintro ⟨b,hb,hxb⟩
  obtain ⟨j,hj⟩ := hcodes b (mem_holes.mp hb).1
  have hOld : original F U j p := by
    change U j ∈ holes F (U p)
    rwa [hj]
  exact hn ⟨j,Or.inl hOld,by rwa [hj]⟩

theorem body_strict {balls : Set (Set X)} (hl : IsLaminar balls)
    (hnf : AvoidsFiniteProperSubballs balls)
    {F : Finset (Set X)} (hF : ∀ b ∈ F, b ∈ balls)
    {U : J → Set X} (hU : ∀ j, U j ∈ balls) (hcodes : ∀ b ∈ F, ∃ j, U j = b)
    {E : J → J → J → Prop}
    (hproper : ∀ h p k, original F U h p → E h p k → U k ⊂ U p)
    (p k : J) (hk : enlarged F U E k p)
    (hnot : ∀ c ∈ holes F (U p), ¬ U k ⊆ c) : body F U E p ⊂ region F (U p) := by
  have hs := enlarged_proper hproper hk
  obtain ⟨x,hx,havoid⟩ := PunctureCuts.exists_avoiding hl hnf (hU k)
    (fun c hc => hF c (mem_holes.mp hc).1) hnot
  have hxOld : x ∈ region F (U p) := by
    rw [region_eq_sdiff_holes]
    exact ⟨hs.1 hx,fun ⟨c,hc,hxc⟩ => havoid c hc hxc⟩
  refine ⟨body_subset_region hcodes E p,?_⟩
  intro hrev
  exact (hrev hxOld).2 ⟨k,hk,hx⟩

theorem body_strict_of_hole_enlargement {balls : Set (Set X)} (hl : IsLaminar balls)
    (hnf : AvoidsFiniteProperSubballs balls)
    {F : Finset (Set X)} (hF : ∀ b ∈ F, b ∈ balls)
    {U : J → Set X} (hU : ∀ j, U j ∈ balls) (hcodes : ∀ b ∈ F, ∃ j, U j = b)
    {E : J → J → J → Prop}
    (hproper : ∀ h p k, original F U h p → E h p k → U k ⊂ U p)
    (p k : J) (hk : enlarged F U E k p) {c : Set X}
    (hc : c ∈ holes F (U p)) (hck : c ⊂ U k) : body F U E p ⊂ region F (U p) := by
  have hcne : c.Nonempty := by
    obtain ⟨x,hx,_⟩ := hnf c (hF c (mem_holes.mp hc).1) ∅ (by simp)
    exact ⟨x,hx⟩
  exact body_strict hl hnf hF hU hcodes hproper p k hk
    (PunctureCuts.not_subset_old_holes (holes_disjoint hl hF (U p)) hc hcne hck)

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {K : Type w₁} {η : Type w₂}
variable {p : Presentation M I κ} {B : Base M I} {q : Presentation M K η}
variable [Finite η]

theorem body_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {F : Finset (Set M)} {U : K → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    (hcodes : ∀ b ∈ F, ∃ j, U j = b)
    (hF : ImaginaryBaseFamilies.Family (L := L) p B q (U ⁻¹' (F : Set (Set M))))
    {E : K → K → K → Prop}
    (hE : OverBase (L := L) p B ((tuplePresentation q (Fin 3)).pullback
      {a | E (a 0) (a 1) (a 2)})) :
    ImaginaryBaseFamilies.Relation (L := L) p B q (body F U E) := by
  have hR : OverBase (L := L) p B ((tuplePresentation q (Fin 2)).pullback
      {a | original F U (a 0) (a 1)}) := by
    have hd := HoleFormulas.holeCodes_definable hp hq hU hF
    rwa [HoleFormulas.holeCodes_eq_pullback hcodes] at hd
  exact PunctureFormulas.puncturedFamily_definable hp hU
    (PunctureFormulas.add_transport_definable hp hq hR hE)

/-- Any finite proper definable addition of holes to the positive regions
of a complete type must leave those regions unchanged. -/
theorem body_eq_region (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {balls : Set (Set M)} (hl : IsLaminar balls)
    (hnf : AvoidsFiniteProperSubballs balls) {F : Finset (Set M)}
    (hF : ∀ b ∈ F, b ∈ balls) {U : K → Set M} (hinj : Function.Injective U)
    (hUballs : ∀ j, U j ∈ balls) (hcodes : ∀ b ∈ F, ∃ j, U j = b)
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    (hSource : ImaginaryBaseFamilies.Family (L := L) p B q (U ⁻¹' (F : Set (Set M))))
    {E : K → K → K → Prop}
    (hE : OverBase (L := L) p B ((tuplePresentation q (Fin 3)).pullback
      {a | E (a 0) (a 1) (a 2)}))
    (hEfin : ∀ i, {k | PunctureFormulas.transported (original F U) E k i}.Finite)
    (hproper : ∀ h i k, original F U h i → E h i k → U k ⊂ U i)
    {A : Set M} (hAtomic : ImaginaryBaseFamilies.CompleteType (L := L) p B A)
    {T : Set K} (hT : ImaginaryBaseFamilies.Family (L := L) p B q T)
    (hpositive : ∀ j ∈ T, U j ∈ F ∧ (region F (U j)).Nonempty ∧ region F (U j) ⊆ A) :
    ∀ j ∈ T, body F U E j = region F (U j) := by
  intro j hj
  have hBody := body_definable hp hq hU hcodes hSource hE
  have hsub : ∀ i ∈ T, region F (U i) ⊆ A := fun i hi => (hpositive i hi).2.2
  have hdis : T.Pairwise fun i k => Disjoint (region F (U i)) (region F (U k)) := by
    intro i hi k hk hik
    exact regions_disjoint hl hF (hpositive i hi).1 (hpositive k hk).1
      (fun he => hik (hinj he))
  have hDC : ∀ i ∈ T, body F U E i ⊆ region F (U i) :=
    fun i _ => body_subset_region hcodes E i
  have hne : ∃ i ∈ T, (body F U E i).Nonempty :=
    ⟨j,hj,body_nonempty hnf hinj hUballs hEfin hproper j⟩
  exact AtomicRegions.refinement_eq hp hAtomic hT hBody hsub hdis hDC hne j hj

end IntegrationInACVF.Section3.DefinableHoleRefinement
