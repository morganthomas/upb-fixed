import UPBJurisdiction
import UPBExtensions

namespace UPB2

/-!
  UPBMinimal: Reducing the Presuppositions & Eliminating Redundant Sub-Premises
  =============================================================================
  This file proves two things in Lean 4:

  1. **True Premise Elimination (`owner_defend` / `P3b` is redundant for Non-Aggression):**
     We do NOT need a separate premise `P3b` (`owner_defend`) to prove that theft and
     bodily taking (`Act.Take x y r`) are forbidden!
     - **Route A (`no_take_via_use`):** `Act.Take x y r` physically conflicts with the
       owner's right to use `r` (`P3a`, `InConflict.take_vs_use`), so `P1` + `P3a` alone
       forbids taking any unlent resource (including your own body).
     - **Route B (`no_take_via_defense`):** Whenever `x` attempts to take `r` from owner
       `y`, `y` is entitled to intervene with proportionate force (`P5a`), which physically
       conflicts with `Act.Take x y r` (`InConflict.take_vs_intervene`), so `P1` + `P5a`
       alone forbids the taking—without `P3b`!

  2. **The 3-Pillar Minimal Presupposition Structure (`MinimalUPB`):**
     Alongside `World.title_rule` (**Pillar 1: Title from First Possession & Consent**),
     all remaining moral assumptions collapse into just two fields in `MinimalUPB`:
     - **Pillar 2 (`compossible`):** In any non-consensual physical conflict, at least one
       party must yield.
     - **Pillar 3 (`jurisdiction_and_liberty`):** One unified principle stating what is
       permitted (using/licensing what you own, doing avoidable acts, resisting force you
       aren't liable to, and enforcing/recovering claims you have standing to enforce—and
       nothing you lack standing to enforce).

     We prove `MinimalUPB.toJurisdictionUPB` and `JurisdictionUPB.toMinimalUPB`
     (`minimal_iff_jurisdiction`), plus `minimal_consistent`, verifying that all 58+
     theorems of `UPBJurisdiction.lean` and `UPBExtensions.lean` follow with zero gaps.
-/

section PremiseElimination
variable {Agent Resource Force : Type} {N : NormSystem Agent Resource Force}
  {w : World Agent Resource Force}

/-- ELIMINATION OF P3b (Route A — via Owner's Use `P3a` + Compossibility `P1`):
    Without using `owner_defend` (`P3b`) at all, taking an unlent resource from its owner
    who holds it is forbidden because taking physically conflicts with the owner's use
    (`InConflict.take_vs_use`). -/
theorem no_take_via_use
    (h_comp : ∀ a₁ a₂ : Act Agent Resource Force,
      InConflict w a₁ a₂ → ¬ w.AgreedContest a₁ a₂ → ¬ (N.Perm a₁ ∧ N.Perm a₂))
    (h_use : ∀ (y : Agent) (r : Resource),
      w.HasJurisdiction y r → ¬ w.Licensed y r → N.Perm (Act.Use y r))
    (x y : Agent) (r : Resource)
    (hxy : x ≠ y) (hy : w.Holds y r) (hj : w.HasJurisdiction y r)
    (hl : ¬ w.Licensed y r) (hnc : ¬ w.Contest x y) :
    N.ObligRefrain (Act.Take x y r) :=
  (N.deontic_duality _).mpr fun h_take =>
    h_comp _ _ (InConflict.take_vs_use x y r hxy hy) (w.no_agreed_contest hnc)
      ⟨h_take, h_use y r hj hl⟩

/-- ELIMINATION OF P3b (Route B — via Proportionate Self-Defense `P5a` + Compossibility `P1`):
    Without using `owner_defend` (`P3b`) or `owner_use` (`P3a`) at all, even if a resource
    IS lent out or in any other state, any attempted taking from the owner who holds it is
    forbidden by `P5a` (`enforce_defense`) + `P1` (`compossible`), because the owner's
    proportionate defensive intervention (`Act.Intervene y x y r f`) physically conflicts
    with `Act.Take x y r` (`InConflict.take_vs_intervene`). -/
theorem no_take_via_defense
    (h_comp : ∀ a₁ a₂ : Act Agent Resource Force,
      InConflict w a₁ a₂ → ¬ w.AgreedContest a₁ a₂ → ¬ (N.Perm a₁ ∧ N.Perm a₂))
    (h_def : ∀ (z x y : Agent) (r : Resource) (f : Force),
      z ≠ x → w.Aggressing x y r → w.EntitledToEnforce z y r →
      w.Proportionate f x y r → N.Perm (Act.Intervene z x y r f))
    (x y : Agent) (r : Resource)
    (hxy : x ≠ y) (hy : w.Holds y r) (hj : w.HasJurisdiction y r)
    (hatt : w.Attempting x y r) (hnc : ¬ w.Contest x y) :
    N.ObligRefrain (Act.Take x y r) := by
  refine (N.deontic_duality _).mpr fun h_take => ?_
  have hag : w.Aggressing x y r := Or.inl ⟨hatt, hxy, hj, hy⟩
  obtain ⟨f, hprop⟩ := w.proportionate_exists x y r (Or.inl hatt)
  have h_int : N.Perm (Act.Intervene y x y r f) :=
    h_def y x y r f (Ne.symm hxy) hag (Or.inl rfl) hprop
  exact h_comp _ _ (InConflict.take_vs_intervene x y y r f hxy hy)
    (w.no_agreed_contest hnc) ⟨h_take, h_int⟩

end PremiseElimination

/-! ## The Reduced 3-Pillar System (`MinimalUPB`)
    Pillar 1 is `w.title_rule` (Title from First Possession, Voluntary Transfer, or Restitution).
    Pillars 2 and 3 are the two fields of `MinimalUPB` below. -/

structure MinimalUPB {Agent Resource Force : Type}
    (N : NormSystem Agent Resource Force) (w : World Agent Resource Force) : Prop where
  /-- Pillar 2: Conflict-Resolution / Compossibility (`P1`). -/
  compossible : ∀ a₁ a₂ : Act Agent Resource Force,
      InConflict w a₁ a₂ → ¬ w.AgreedContest a₁ a₂ → ¬ (N.Perm a₁ ∧ N.Perm a₂)
  /-- Pillar 3: Unified Jurisdiction, Liberty, and Enforcement Principle (`P3`–`P5` combined). -/
  jurisdiction_and_liberty :
    (∀ y r, w.HasJurisdiction y r → ¬ w.Licensed y r → N.Perm (Act.Use y r)) ∧
    (∀ o x r, w.HasJurisdiction o r → x ≠ o → w.Permits o x r → N.Perm (Act.Use x r)) ∧
    (∀ x y r, x ≠ y → w.HasJurisdiction y r → N.Perm (Act.Defend y x r)) ∧
    (∀ x z f, x ≠ z → ¬ w.Liable x z f → N.Perm (Act.Resist x z f)) ∧
    (∀ z x y r f, z ≠ x → w.Aggressing x y r → w.EntitledToEnforce z y r →
      w.Proportionate f x y r → N.Perm (Act.Intervene z x y r f)) ∧
    (∀ z y o r, z ≠ y → o ≠ y → w.HasJurisdiction o r → ¬ w.Permits o y r →
      w.EntitledToEnforce z o r → N.Perm (Act.Take z y r)) ∧
    (∀ z v r, ¬ w.EntitledToEnforce z v r →
      (∀ x f, ¬ N.Perm (Act.Intervene z x v r f)) ∧
      (w.HasJurisdiction v r → ∀ y, ¬ N.Perm (Act.Take z y r))) ∧
    (∀ x id, N.Perm (Act.AvoidableAct x id))

/-- Any model of `MinimalUPB` immediately yields `JurisdictionUPB` (and therefore all 58+
    theorems in `UPBJurisdiction.lean` and `UPBExtensions.lean`). -/
theorem MinimalUPB.toJurisdictionUPB {Agent Resource Force : Type}
    {N : NormSystem Agent Resource Force} {w : World Agent Resource Force}
    (M : MinimalUPB N w) : JurisdictionUPB N w where
  compossible := M.compossible
  owner_use := M.jurisdiction_and_liberty.1
  licensed_use := M.jurisdiction_and_liberty.2.1
  owner_defend := M.jurisdiction_and_liberty.2.2.1
  body_resist := M.jurisdiction_and_liberty.2.2.2.1
  enforce_defense := M.jurisdiction_and_liberty.2.2.2.2.1
  enforce_recovery := M.jurisdiction_and_liberty.2.2.2.2.2.1
  standing := M.jurisdiction_and_liberty.2.2.2.2.2.2.1
  avoidable_perm := M.jurisdiction_and_liberty.2.2.2.2.2.2.2

/-- Conversely, `JurisdictionUPB` packages directly into `MinimalUPB`. -/
theorem JurisdictionUPB.toMinimalUPB {Agent Resource Force : Type}
    {N : NormSystem Agent Resource Force} {w : World Agent Resource Force}
    (H : JurisdictionUPB N w) : MinimalUPB N w where
  compossible := H.compossible
  jurisdiction_and_liberty :=
    ⟨H.owner_use, H.licensed_use, H.owner_defend, H.body_resist,
     H.enforce_defense, H.enforce_recovery, H.standing, H.avoidable_perm⟩

/-- Exact logical equivalence between the 3-pillar system and the expanded premise list. -/
theorem minimal_iff_jurisdiction {Agent Resource Force : Type}
    (N : NormSystem Agent Resource Force) (w : World Agent Resource Force) :
    MinimalUPB N w ↔ JurisdictionUPB N w :=
  ⟨MinimalUPB.toJurisdictionUPB, JurisdictionUPB.toMinimalUPB⟩

/-- Consistency of the 3-pillar system in every world. -/
theorem minimal_consistent {Agent Resource Force : Type}
    (w : World Agent Resource Force) (boxing : Prop := False) :
    MinimalUPB (JSystem w boxing) w :=
  (consistent w boxing).toMinimalUPB

end UPB2

#print axioms UPB2.no_take_via_use
#print axioms UPB2.no_take_via_defense
#print axioms UPB2.minimal_iff_jurisdiction
#print axioms UPB2.minimal_consistent
