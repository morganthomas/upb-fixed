import UPBJurisdiction

namespace UPB2

/-!
  Extension 1: Threats (F1)
  =========================
  Derivative prohibition of wrongful threats: threatening an act `a` is permitted only if
  `a` itself is permitted (`Perm (Threaten x a) → Perm a`, or equivalently by duality,
  `ObligRefrain a → ObligRefrain (Threaten x a)`).
-/

structure ThreatRules {Agent Resource Force : Type} (N : NormSystem Agent Resource Force) where
  PermThreat : Agent → Act Agent Resource Force → Prop
  ObligRefrainThreat : Agent → Act Agent Resource Force → Prop
  threat_duality : ∀ x a, ObligRefrainThreat x a ↔ ¬ PermThreat x a
  threat_requires_perm : ∀ x a, PermThreat x a → N.Perm a

section ThreatTheorems
variable {Agent Resource Force : Type} {N : NormSystem Agent Resource Force}
  {w : World Agent Resource Force}

/-- Core lemma: if `a` is forbidden (`ObligRefrain a`), threatening `a` is forbidden. -/
theorem no_threat_of_forbidden (T : ThreatRules N) (x : Agent) (a : Act Agent Resource Force)
    (h : N.ObligRefrain a) : T.ObligRefrainThreat x a :=
  (T.threat_duality x a).mpr fun hp =>
    (N.deontic_duality a).mp h (T.threat_requires_perm x a hp)

/-- F1a: Threatening to take an owned thing from its owner is forbidden. -/
theorem no_threat_to_take (H : JurisdictionUPB N w) (T : ThreatRules N) (x y : Agent)
    (r : Resource) (hxy : x ≠ y) (hy : w.Holds y r) (hj : w.HasJurisdiction y r)
    (hnc : ¬ w.Contest x y) :
    T.ObligRefrainThreat x (Act.Take x y r) :=
  no_threat_of_forbidden T x _ (no_take_from_owner H x y r hxy hy hj hnc)

/-- F1b: Threatening to strike or kill a peaceful person is forbidden. -/
theorem no_threat_to_assault_peaceful (H : JurisdictionUPB N w) (T : ThreatRules N)
    (z x : Agent) (f : Force) (hzx : z ≠ x) (hpeace : ∀ v r, ¬ w.Aggressing x v r)
    (hnc : ¬ w.Contest z x) :
    T.ObligRefrainThreat z (Act.Strike z x f) :=
  no_threat_of_forbidden T z _ (no_assault_on_peaceful H z x f hzx hpeace hnc).1

/-- F1c: Threatening to forcibly stop someone from doing what they are permitted to do
    (including avoidable acts or using their own property/road) is forbidden. -/
theorem no_threat_to_stop_permitted (H : JurisdictionUPB N w) (T : ThreatRules N)
    (z : Agent) (a : Act Agent Resource Force) (hz : z ≠ a.doer) (ha : N.Perm a)
    (hnc : ¬ w.Contest z a.doer) :
    T.ObligRefrainThreat z (Act.Stop z a) :=
  no_threat_of_forbidden T z _ (no_stopping_permitted_acts H z a hz ha hnc)

end ThreatTheorems

/-- Extended aggression relation covering:
    (1) the original `w.Aggressing x o r` (taking from owner `o` or neglecting dependent `o`),
    (2) fleeing with / refusing to yield `o`'s property `r` (`FleeingWith x r`), and
    (3) an unauthorized party `x` (`¬ w.EntitledToEnforce x o r`) trying to take `o`'s
        property `r` from a third-party holder `h` (thief-from-thief). -/
def World.AggressingExtended {Agent Resource Force : Type}
    (w : World Agent Resource Force) (FleeingWith : Agent → Resource → Prop)
    (x o : Agent) (r : Resource) : Prop :=
  w.Aggressing x o r ∨
  (x ≠ o ∧ w.HasJurisdiction o r ∧ w.Holds x r ∧ ¬ w.Permits o x r ∧ FleeingWith x r) ∨
  (∃ h, x ≠ o ∧ x ≠ h ∧ w.HasJurisdiction o r ∧ w.Holds h r ∧
    w.Attempting x h r ∧ ¬ w.EntitledToEnforce x o r)

/-- Key property: legitimate recovery by the owner `o` or any entitled rescuer `z`
    (`w.EntitledToEnforce z o r`) is NEVER classified as `AggressingExtended` against `o`. -/
theorem recovery_not_aggression {Agent Resource Force : Type}
    (w : World Agent Resource Force) (FleeingWith : Agent → Resource → Prop)
    (z o : Agent) (r : Resource)
    (hent : w.EntitledToEnforce z o r)
    (hnot_att_owner : ¬ (w.Attempting z o r ∧ z ≠ o ∧ w.HasJurisdiction o r ∧ w.Holds o r))
    (hnot_neglect : ¬ (r = w.body o ∧ w.Neglects z o))
    (hnot_flee : ¬ FleeingWith z r) :
    ¬ w.AggressingExtended FleeingWith z o r := by
  rintro ((h1 | h2) | ⟨_, _, _, _, hf⟩ | ⟨h, _, _, _, _, _, hne⟩)
  · exact hnot_att_owner h1
  · exact hnot_neglect h2
  · exact hnot_flee hf
  · exact hne hent

end UPB2
