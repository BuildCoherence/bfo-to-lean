import BFO

/-! BFO theorems over the generated `BFO` bundle.

This file is the third CI fidelity check and carries two sub-libraries:

* *Structural fidelity witnesses* — top-level theorems stating pure
  structural consequences of the bundle. They fail elaboration if the
  relevant axiom is missing, renamed, or mistranslated.

* *Canonical demo scenarios* — one `structure` per scenario bundling
  the scenario's entity `Type`s and propositional hypotheses, plus
  theorems taking `(b : BFO) (s : <ScenarioStructure>)` that chain
  BFO bundle axioms with `s.<field>` to derive consequences. Each
  mirrors a BFO example found in the literature. (Added below
  the structural witnesses.)

`open BFO` brings the generated vocabulary (`InstanceOf`, `MaterialEntity`,
…) and the adoption bundle `BFO` into scope; the bundle `extends`
every module bundle, so each axiom is reachable directly as `b.<field>`.
-/

namespace BfoToLean.Theorems

open BFO

/-- `[eld-1]` declares `continuant-part-of` and `has-continuant-part`
are inverse — the BFO bundle therefore lets us flip one to the other
and back. -/
theorem eld_1_witness (b : BFO) :
    ∀ (t a c : Type), ContinuantPartOf a c t ↔ HasContinuantPart c a t := by
  intro t a c
  exact b.eld_1 t a c

/-- The `BFO` bundle is not vacuously `True`: it carries axiom
`[qkp-1]` — "universals are not particulars". This theorem asserts
that adopting `BFO` rules out the absurd `∃ x. universal x ∧
particular x`. -/
theorem qkp_1_witness (b : BFO) :
    ¬ ∃ (x : Type), Universal x ∧ Particular x :=
  b.qkp_1

/-- The `BFO` bundle's transitivity-of-precedence axiom `[ctz-1]`
gives transitivity of `precedes` as a corollary, demonstrating that
the bundle is usable for ordinary inference. -/
theorem precedes_transitive (b : BFO) :
    ∀ (a c d : Type), Precedes a c → Precedes c d → Precedes a d := by
  intro a c d hac hcd
  exact b.ctz_1 a c d ⟨hac, hcd⟩

/-! ## Canonical demo scenarios

Each scenario below bundles a BFO example from the literature as a
`structure` carrying the scenario's entity `Type`s and propositional
hypotheses. Its theorems take `(b : BFO) (s : <ScenarioStructure>)`
and chain BFO bundle axioms (`b.<axiom_id>`) with scenario
hypotheses (`s.<field>`) to derive a consequence.
-/

/-- Glass shattering on impact (Smith/Arp/Spear's recurring example
of a *specifically dependent realizable*). A piece of glass bears a
fragility (a disposition), and a shattering event realizes that
fragility. Exercises the realization-domain axiom `[oot-1]` from the
specific-dependency module. -/
structure GlassFragilityShattering where
  glass : Type
  fragility : Type
  shattering : Type
  t : Type
  glass_is_material             : InstanceOf glass MaterialEntity t
  fragility_depends_on_glass    : SpecificallyDependsOn fragility glass
  shattering_realizes_fragility : Realizes shattering fragility

/-- From the realization-domain axiom `[oot-1]`, the realizing entity
is a process at some time. -/
theorem shattering_is_process (b : BFO) (s : GlassFragilityShattering) :
    ∃ (t : Type), InstanceOf s.shattering Process t :=
  (b.oot_1 s.shattering s.fragility
    s.shattering_realizes_fragility).left

/-- From the realization-domain axiom `[oot-1]`, the realized entity
is a realizable entity at some time. -/
theorem fragility_is_realizable (b : BFO) (s : GlassFragilityShattering) :
    ∃ (t : Type), InstanceOf s.fragility RealizableEntity t :=
  (b.oot_1 s.shattering s.fragility
    s.shattering_realizes_fragility).right

/-- `[pvk-1]`'s inverse pairing lets us derive that the fragility has
the shattering as a realization. -/
theorem fragility_has_realization (b : BFO) (s : GlassFragilityShattering) :
    HasRealization s.fragility s.shattering :=
  (b.pvk_1 s.shattering s.fragility).mp
    s.shattering_realizes_fragility

/-- Flock-and-birds object-aggregate membership (Smith et al., *On
Classes and Collections*). Two birds are member-parts of a flock at
some time; the flock is an object aggregate, the birds are objects.
Exercises member-part axioms `[dvq-1]` and `[jrm-1]` from the
material-entity module. -/
structure ObjectAggregateMembership where
  flock : Type
  bird1 : Type
  bird2 : Type
  t : Type
  bird1_member_of_flock : MemberPartOf bird1 flock t
  bird2_member_of_flock : MemberPartOf bird2 flock t

/-- From the member-part domain/range axiom `[dvq-1]`, the flock is
an object aggregate at the witnessing time. -/
theorem flock_is_object_aggregate (b : BFO) (s : ObjectAggregateMembership) :
    InstanceOf s.flock ObjectAggregate s.t :=
  (b.dvq_1 s.bird1 s.flock s.t s.bird1_member_of_flock).right.left

/-- From `[dvq-1]`, the first bird is an object at the witnessing
time. -/
theorem bird1_is_object (b : BFO) (s : ObjectAggregateMembership) :
    InstanceOf s.bird1 Object s.t :=
  (b.dvq_1 s.bird1 s.flock s.t s.bird1_member_of_flock).left

/-- From the member-part inversion axiom `[jrm-1]`, the flock
has-member-part the bird. -/
theorem flock_has_member_part_bird1 (b : BFO) (s : ObjectAggregateMembership) :
    HasMemberPart s.flock s.bird1 s.t :=
  (b.jrm_1 s.t s.bird1 s.flock).mp s.bird1_member_of_flock

/-- PDF-as-generically-dependent (Smith/Arp/Spear's recurring example
of a *generically dependent continuant*). A PDF file (gdc) is
concretized by a bit-pattern (sdc) inhering in a disk (independent
continuant) at some time; the gdc is then generically-dependent on
the disk. Exercises the gdc-concretization axiom `[cik-1]` and the
gdc-domain/range axiom `[ekp-1]` from the generic-dependence module. -/
structure PdfAsGenericallyDependent where
  pdf : Type
  pattern : Type
  disk : Type
  t : Type
  pdf_is_gdc              : InstanceOf pdf GenericallyDependentContinuant t
  pattern_is_sdc          : InstanceOf pattern SpecificallyDependentContinuant t
  disk_is_independent     : InstanceOf disk IndependentContinuant t
  pattern_concretizes_pdf : Concretizes pattern pdf t
  pattern_inheres_in_disk : InheresIn pattern disk

/-- The concretization-implies-generic-dependence axiom `[cik-1]`
gives us that the PDF generically-depends-on the disk at `t`. -/
theorem pdf_generically_depends_on_disk
    (b : BFO) (s : PdfAsGenericallyDependent) :
    GenericallyDependsOn s.pdf s.disk s.t :=
  b.cik_1 s.pdf s.disk s.pattern
    ⟨⟨s.t, s.pdf_is_gdc⟩, ⟨s.t, s.pattern_is_sdc⟩, ⟨s.t, s.disk_is_independent⟩⟩
    s.t ⟨s.pattern_concretizes_pdf, s.pattern_inheres_in_disk⟩

/-- The generic-dependence inversion axiom `[mvp-1]` lets us flip
the derived `genericallyDependsOn` to `isCarrierOf`. -/
theorem disk_is_carrier_of_pdf (b : BFO) (s : PdfAsGenericallyDependent) :
    IsCarrierOf s.disk s.pdf s.t :=
  (b.mvp_1 s.t s.pdf s.disk).mp
    (pdf_generically_depends_on_disk b s)

/-- Red apple — a quality (redness) inheres in its bearer (an apple).
Exercises `[tht-1]`, the canonical "inherence ⇒ specific dependence"
axiom from the specific-dependency module. -/
structure QualityInheresInBearer where
  redness : Type
  apple : Type
  t : Type
  apple_is_independent    : InstanceOf apple IndependentContinuant t
  redness_inheres_in_apple : InheresIn redness apple

/-- The forward direction of `[tht-1]` extracts
`specificallyDependsOn` from `inheresIn`. -/
theorem redness_depends_on_apple (b : BFO) (s : QualityInheresInBearer) :
    SpecificallyDependsOn s.redness s.apple :=
  ((b.tht_1 s.redness s.apple).mp s.redness_inheres_in_apple).left

/-- `[dzz-1]` (the `inheresIn ↔ bearerOf` inversion) lets us flip
the scenario's inherence claim. -/
theorem apple_is_bearer_of_redness (b : BFO) (s : QualityInheresInBearer) :
    BearerOf s.apple s.redness :=
  (b.dzz_1 s.redness s.apple).mp s.redness_inheres_in_apple

/-- `[tht-1]`'s right-hand side carries a disjointness clause: a
quality's bearer is not a spatial region. Exercising it gives the
demo-scenario layer at least one negation/disjointness check
(complementing the structural `qkp_1_witness`). -/
theorem apple_is_not_spatial_region (b : BFO) (s : QualityInheresInBearer) :
    ∃ (t : Type), ¬ InstanceOf s.apple SpatialRegion t := by
  have h := (b.tht_1 s.redness s.apple).mp s.redness_inheres_in_apple
  obtain ⟨t, _, _, hNotSpatial⟩ := h.right
  exact ⟨t, hNotSpatial⟩

end BfoToLean.Theorems
