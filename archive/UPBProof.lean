/-
  UPB Supplement: Machine-Verified Formalization in Lean 4 (v4.35.0)
  ===================================================================
  Formalizing the Repaired "Universally Preferable Behavior" (UPB) Deductive Engine
  with Explicit Presuppositions (No "May = Must" Fallacy, Zero Custom Global Axioms).
-/

namespace UPB

/-- Elementary interpersonal actions between two agents (`Agent`) regarding a
    scarce resource (`Resource`):
    - `UseOwn x r`: `x` peacefully uses resource `r` within `x`'s jurisdiction
    - `Coerce x y r`: `x` initiates unconsented force against `y` to seize/override `r`
    - `Defend y x r`: `y` uses defensive force to repel `x`'s active coercion over `r`
    - `AvoidableAct x id`: `x` performs a non-invasive action that others can freely avoid -/
inductive Act (Agent Resource : Type) where
  | UseOwn       (x : Agent) (r : Resource) : Act Agent Resource
  | Coerce       (x y : Agent) (r : Resource) : Act Agent Resource
  | Defend       (y x : Agent) (r : Resource) : Act Agent Resource
  | AvoidableAct (x : Agent) (id : Nat) : Act Agent Resource

/-- A Deontic Norm System specifies which actions are Permissible (`Perm`)
    and which actions agents are Obligated to Refrain from (`ObligRefrain`),
    satisfying standard deontic duality: `ObligRefrain a ↔ ¬ Perm a`. -/
structure NormSystem (Agent Resource : Type) where
  Perm : Act Agent Resource → Prop
  ObligRefrain : Act Agent Resource → Prop
  deontic_duality : ∀ a : Act Agent Resource, ObligRefrain a ↔ ¬ Perm a

/-- Jurisdictional assignment: `HasJurisdiction x r` means `x` holds rightful
    peaceful title over resource `r` (either `x`'s own body `body x` or a peacefully
    appropriated/transferred external resource). -/
structure JurisdictionModel (Agent Resource : Type) where
  body : Agent → Resource
  body_injective : ∀ (x y : Agent), body x = body y → x = y
  HasJurisdiction : Agent → Resource → Prop
  /-- Presupposition P5a (Self-Sovereignty): Every agent holds jurisdiction over their own body. -/
  self_sovereignty : ∀ x : Agent, HasJurisdiction x (body x)
  /-- Exclusivity of rivalrous jurisdiction: a scarce resource cannot be under
      two conflicting exclusive jurisdictions at the same time. -/
  exclusive_jurisdiction : ∀ (x y : Agent) (r : Resource),
    HasJurisdiction x r → HasJurisdiction y r → x = y

/-- Two actions are `InConflict` (normatively incompossible) when simultaneous
    exercise produces a direct physical collision over the same scarce resource:
    1. Bilateral coercion (`Coerce x y r` and `Coerce y x r`), or
    2. Unilateral coercion (`Coerce x y r`) colliding with the rightful holder's
       peaceful exercise (`UseOwn y r`) or defensive repulsion (`Defend y x r`). -/
inductive InConflict {Agent Resource : Type} (J : JurisdictionModel Agent Resource) :
    Act Agent Resource → Act Agent Resource → Prop where
  | mutual_coercion (x y : Agent) (r : Resource) (hxy : x ≠ y) :
      InConflict J (Act.Coerce x y r) (Act.Coerce y x r)
  | coerce_vs_use (x y : Agent) (r : Resource) (hxy : x ≠ y)
      (hj : J.HasJurisdiction y r) :
      InConflict J (Act.Coerce x y r) (Act.UseOwn y r)
  | coerce_vs_defend (x y : Agent) (r : Resource) (hxy : x ≠ y)
      (hj : J.HasJurisdiction y r) :
      InConflict J (Act.Coerce x y r) (Act.Defend y x r)

/-- THE EXPLICIT PRESUPPOSITIONS OF A REPAIRED UPB SYSTEM (`RepairedUPB`):
    Instead of equating `Perm` ("may") with `Oblig` ("must"), we state the exact
    presuppositions required for a peaceful, symmetric interpersonal ethic: -/
structure RepairedUPB {Agent Resource : Type}
    (N : NormSystem Agent Resource) (J : JurisdictionModel Agent Resource) : Prop where
  /-- Presupposition P1 (Compossibility / Conflict-Free Norms):
      A valid moral system cannot simultaneously permit two actions that are in direct conflict. -/
  compossible : ∀ a₁ a₂ : Act Agent Resource,
      InConflict J a₁ a₂ → ¬ (N.Perm a₁ ∧ N.Perm a₂)

  /-- Presupposition P2 (Agent Symmetry / No 'Might Makes Right' or Caste Privilege):
      If the norm system permits agent `x` to coercively override `y` over resource `r`,
      symmetry across agents requires that it equally permits `y` to coercively override `x`. -/
  agent_symmetry_coercion : ∀ (x y : Agent) (r : Resource),
      N.Perm (Act.Coerce x y r) → N.Perm (Act.Coerce y x r)

  /-- Presupposition P3 (Jurisdictional Use & Defensive Standing):
      If `y` holds rightful jurisdiction over `r`, `y` is permitted to peacefully use `r`
      and is permitted to defend `r` against active coercion by another agent `x`. -/
  rightful_use_perm : ∀ (y : Agent) (r : Resource),
      J.HasJurisdiction y r → N.Perm (Act.UseOwn y r)
  rightful_defend_perm : ∀ (x y : Agent) (r : Resource),
      x ≠ y → J.HasJurisdiction y r → N.Perm (Act.Defend y x r)

  /-- Presupposition P4 (Liberty of Avoidable, Non-Invasive Actions):
      Actions that do not cross another's bodily or property boundaries (`AvoidableAct`)
      conflict with no rightful action and are therefore permissible. -/
  avoidable_perm : ∀ (x : Agent) (id : Nat), N.Perm (Act.AvoidableAct x id)

/- ============================================================================
   MACHINE-VERIFIED THEOREMS OF THE REPAIRED UPB SYSTEM
   ============================================================================ -/

/-- THEOREM 1A (Via Stef's "Tarantino Morality" Bilateral Symmetry Route):
    Using ONLY `compossible` (P1) and `agent_symmetry_coercion` (P2),
    NO agent has permission to initiate coercion against any other distinct agent. -/
theorem no_perm_coerce_via_symmetry {Agent Resource : Type}
    (N : NormSystem Agent Resource) (J : JurisdictionModel Agent Resource)
    (H : RepairedUPB N J) (x y : Agent) (r : Resource) (hxy : x ≠ y) :
    ¬ N.Perm (Act.Coerce x y r) := by
  intro h_perm_xy
  have h_perm_yx : N.Perm (Act.Coerce y x r) :=
    H.agent_symmetry_coercion x y r h_perm_xy
  have h_conf : InConflict J (Act.Coerce x y r) (Act.Coerce y x r) :=
    InConflict.mutual_coercion x y r hxy
  exact H.compossible (Act.Coerce x y r) (Act.Coerce y x r) h_conf ⟨h_perm_xy, h_perm_yx⟩

/-- THEOREM 1B (Via Jurisdictional Defense Route — Independent Proof):
    Even WITHOUT `agent_symmetry_coercion` (P2), if `y` holds rightful jurisdiction
    over `r`, `compossible` (P1) + `rightful_defend_perm` (P3) independently prove
    that `x` has no permission to coerce `y` over `r`. -/
theorem no_perm_coerce_via_jurisdiction {Agent Resource : Type}
    (N : NormSystem Agent Resource) (J : JurisdictionModel Agent Resource)
    (H : RepairedUPB N J) (x y : Agent) (r : Resource) (hxy : x ≠ y)
    (hj : J.HasJurisdiction y r) :
    ¬ N.Perm (Act.Coerce x y r) := by
  intro h_perm_xy
  have h_def : N.Perm (Act.Defend y x r) :=
    H.rightful_defend_perm x y r hxy hj
  have h_conf : InConflict J (Act.Coerce x y r) (Act.Defend y x r) :=
    InConflict.coerce_vs_defend x y r hxy hj
  exact H.compossible (Act.Coerce x y r) (Act.Defend y x r) h_conf ⟨h_perm_xy, h_def⟩

/-- THEOREM 1C (Deontic Equivalence — From `¬ May` to `Must Not`):
    By standard deontic duality (`ObligRefrain a ↔ ¬ Perm a`), every agent is
    morally obligated to refrain from initiating force (`ObligRefrain (Coerce x y r)`). -/
theorem oblig_refrain_coerce {Agent Resource : Type}
    (N : NormSystem Agent Resource) (J : JurisdictionModel Agent Resource)
    (H : RepairedUPB N J) (x y : Agent) (r : Resource) (hxy : x ≠ y) :
    N.ObligRefrain (Act.Coerce x y r) := by
  rw [N.deontic_duality]
  exact no_perm_coerce_via_symmetry N J H x y r hxy

/-- THEOREM 2 (Bodily Non-Aggression — Prohibition of Rape, Assault, and Murder):
    For any two distinct agents `x` and `y`, `x` is obligated to refrain from
    coercing `y`'s body (`J.body y`), and `y` is permitted to defend `J.body y`. -/
theorem bodily_non_aggression {Agent Resource : Type}
    (N : NormSystem Agent Resource) (J : JurisdictionModel Agent Resource)
    (H : RepairedUPB N J) (x y : Agent) (hxy : x ≠ y) :
    N.ObligRefrain (Act.Coerce x y (J.body y)) ∧ N.Perm (Act.Defend y x (J.body y)) := by
  refine ⟨oblig_refrain_coerce N J H x y (J.body y) hxy, ?_⟩
  exact H.rightful_defend_perm x y (J.body y) hxy (J.self_sovereignty y)

/-- THEOREM 3 (Property Non-Aggression — Prohibition of Theft):
    Whenever `y` holds rightful jurisdiction over an external resource `r`,
    any distinct agent `x` is obligated to refrain from coercively taking `r`,
    and `y` is permitted to peacefully use and defend `r`. -/
theorem property_non_aggression {Agent Resource : Type}
    (N : NormSystem Agent Resource) (J : JurisdictionModel Agent Resource)
    (H : RepairedUPB N J) (x y : Agent) (r : Resource) (hxy : x ≠ y)
    (hj : J.HasJurisdiction y r) :
    N.ObligRefrain (Act.Coerce x y r) ∧ N.Perm (Act.UseOwn y r) := by
  exact ⟨oblig_refrain_coerce N J H x y r hxy, H.rightful_use_perm y r hj⟩

/-- THEOREM 4 (Elimination of Statist "Middle Truths" / Role Exemptions):
    Let `Official : Agent → Prop` be any institutional title, badge, or majority mandate.
    Under `RepairedUPB`, holding `Official x` grants zero exemption from the prohibition
    on initiating coercion against peaceful agents. -/
theorem no_official_exemption {Agent Resource : Type}
    (N : NormSystem Agent Resource) (J : JurisdictionModel Agent Resource)
    (H : RepairedUPB N J) (Official : Agent → Prop)
    (x y : Agent) (r : Resource) (hxy : x ≠ y) :
    Official x → N.ObligRefrain (Act.Coerce x y r) := by
  intro _
  exact oblig_refrain_coerce N J H x y r hxy

/-- Canonical Non-Aggression NormSystem `NAPSystem J` for consistency verification. -/
def NAPSystem {Agent Resource : Type} (J : JurisdictionModel Agent Resource) :
    NormSystem Agent Resource where
  Perm a :=
    match a with
    | Act.UseOwn x r       => J.HasJurisdiction x r
    | Act.Coerce _ _ _     => False
    | Act.Defend y x r     => x ≠ y ∧ J.HasJurisdiction y r
    | Act.AvoidableAct _ _ => True
  ObligRefrain a :=
    match a with
    | Act.UseOwn x r       => ¬ J.HasJurisdiction x r
    | Act.Coerce _ _ _     => True
    | Act.Defend y x r     => ¬ (x ≠ y ∧ J.HasJurisdiction y r)
    | Act.AvoidableAct _ _ => False
  deontic_duality a := by
    cases a <;> simp

/-- THEOREM 5 (Consistency / Satisfiability of the Repaired UPB Presuppositions):
    For any `JurisdictionModel J`, `NAPSystem J` satisfies all presuppositions of `RepairedUPB`.
    This proves that the presupposition set is 100% consistent and non-vacuous. -/
theorem repaired_upb_consistent {Agent Resource : Type}
    (J : JurisdictionModel Agent Resource) :
    RepairedUPB (NAPSystem J) J where
  compossible a₁ a₂ h_conf := by
    intro ⟨h₁, _⟩
    cases h_conf with
    | mutual_coercion  => exact h₁
    | coerce_vs_use    => exact h₁
    | coerce_vs_defend => exact h₁
  agent_symmetry_coercion _ _ _ h_perm := False.elim h_perm
  rightful_use_perm _ _ hj := hj
  rightful_defend_perm _ _ _ hxy hj := ⟨hxy, hj⟩
  avoidable_perm _ _ := True.intro

end UPB

#print axioms UPB.oblig_refrain_coerce
#print axioms UPB.no_perm_coerce_via_jurisdiction
#print axioms UPB.bodily_non_aggression
#print axioms UPB.property_non_aggression
#print axioms UPB.no_official_exemption
#print axioms UPB.repaired_upb_consistent
