# Premises of the Jurisdiction-Route Formalization

This note states, in plain English, every assumption behind `UPBJurisdiction.lean`. This is the version of the repaired UPB argument that drops the agent-symmetry premise (P2). Lean has checked that all of the file's theorems follow from these assumptions and that the assumptions are consistent with each other. Whether the assumptions are true is a separate question. See `Limitations.md` for what the model leaves out.

The Lean name of each assumption is given in parentheses so you can find it in the code.

## Title

- **P0, Title from first possession and consensual transfer** (`title_rule`, using `History.TitleAt`). Time runs in steps. At any time, you have rightful title to something exactly when one of these holds:
  - you became its first possessor at that time;
  - you had title at the previous step and didn't voluntarily transfer it;
  - at the previous step, its owner voluntarily transferred it to you, by gift, sale or other consensual transfer; or
  - at the previous step, its owner owed you a payment that was due, either as compensation for a past wrong (**restitution**) or under a contract, and it was designated as part of that payment.

  A transfer is **voluntary** (`ValidGift`) when it wasn't induced by deception, wasn't made under threat of initiated force, and was made by someone with the **capacity to choose**. Nothing else creates or moves title. A "gift" or "sale" from someone without title passes nothing, and neither does a handover obtained by fraud or under duress.

  **Restitution** works under **strict liability** (`Wronged`, `wrong_creates_debt`). You wrong someone if you take from them something they own, destroy or damage something they own, or injure them. No fault is needed, and no excuse removes the wrong. Every wrong creates a debt to the victim, which stays owed until it is paid off. Only the wrongdoer's own transferable property can pass as compensation, but that includes property they acquire long after the wrong, so unpaid debts don't lapse.

  **Contracts** (`ValidAgreement`, `Incurs`) follow the **title-transfer theory** (Rothbard, Evers). A contract is an agreement under which you will owe someone something, now or later, possibly on conditions: repaying a loan, paying for a meal, forfeiting a deposit if you fail to deliver. A valid contract creates a debt in the same way a wrong does, paid from your property. Agreement can be explicit or by conduct, such as ordering a meal. A contract counts only if your agreement wasn't induced by deception, wasn't made under threat of initiated force, and was made while you had the capacity to choose. Breaking a contract isn't a further wrong: any penalty for breach has to be part of the contract. A promise to *perform* (to work, say) isn't enforceable as such, since bodies can't be transferred; only a stipulated forfeiture of property is.

  **Priority** (`first_in_time`). A debtor's property can go to a creditor only once every creditor with an older claim has been paid off. Victims of wrongs and contract creditors share **one queue**, ranked by when each debt was first incurred. A creditor's claim also takes priority over a gift the debtor makes at the same moment.
- **P0b, Bodies can't be transferred** (`body_inalienable`). Title to a person's body can't be given away, so there is no voluntary slavery. This is contested; some libertarians accept voluntary slavery contracts. It is kept as a separate premise so it can be dropped. Without it, self-ownership would hold only for people who have not given their body away.

Self-ownership, exclusivity of title and acquisition of unowned things used to be separate premises. They are now theorems, derived from P0, P0b and the physical facts below (see `Conclusions.md`).

## Physical facts

These are assumed to hold in every situation the model considers (fields of `World`). They describe what is physically the case, not what anyone may or may not do.

1. **Bodies** (`body`, `body_injective`). Each person has a body, and different people have different bodies.
2. **Bodily control** (`holds_body`). Every person physically controls their own body.
3. **First possession of one's body** (`body_first`). Every person became the first possessor of their own body at some time up to now.
4. **Unique first possessor** (`first_unique`). A thing has only one first possessor, who first possessed it at only one time.
5. **One recipient at a time** (`gave_unique`). No one can hand the same thing to two different people at the same moment.
   - A parallel assumption about the undefined term "compensates" (`compensation_unique`): a single thing pays only one creditor at a time.
6. **One licensee at a time** (`permits_unique`). An owner can permit only one person at a time to use a scarce thing, since two people can't use it at once.
7. **Held things were possessed first by someone** (`held_has_first`). Anything someone currently holds was first possessed by someone at some time up to now.
8. **Proportionate force exists** (`proportionate_exists`). Whenever someone is trying to take something, or a guardian is keeping custody without providing care, there is some proportionate amount of force that could be used to stop them. Strictly, this is an assumption about the undefined term "proportionate", described below.

A situation also records facts that vary from case to case. First, its **history** (`hist`), which records:
- who first possessed what, and when (`FirstAt`);
- who handed what to whom, and when (`GaveAt`), and which handovers were induced by deception (`DeceivedAt`) or made under threat of force (`CoercedAt`);
- which things are transferable (`Alienable`);
- who had the capacity to choose, and when (`Capable`);
- a **record of wrongs**: who took what from whom (`TookAt`), who destroyed or damaged what (`DestroyedAt`), and who injured whom other than in permitted defense or enforcement (`InjuredAt`);
- a **record of agreements**: who agreed to owe whom (`AgreedAt`), and which agreements were induced by deception (`AgreementDeceivedAt`) or made under threat (`AgreementCoercedAt`);
- which debts are still owed (`Outstanding`) and what is designated as payment (`CompensatesAt`), both undefined terms described below.

It also records the present situation:
- the present time (`now`);
- who currently holds what (`Holds`);
- which owners currently permit whom to use which of their things (`Permits`), as in lending, renting or inviting a guest;
- who is currently trying to take what from whom (`Attempting`);
- which owners have declined help from others for which of their things (`Declines`);
- who currently has custody of which dependents (`Guardian`), and whether they are providing adequate care (`Provides`).

## Undefined terms

- **Force** (`Force`). Ways of using force against someone. Nothing is assumed about them: they need not be measured on a scale or ordered.
- **Proportionate** (`Proportionate`). Whether a given use of force is proportionate as a means of stopping a given aggression. This is deliberately left undefined. The only thing assumed about it is physical fact 8 above. Every theorem holds for every meaning of "proportionate" that satisfies fact 8, so the formalization takes no side on which uses of force count as proportionate in specific cases.

- **Still owed** (`Outstanding`). Whether someone owes another a payment that is due and not yet made, as compensation or under a contract. Deliberately left undefined, so the model needs no unit of value and takes no position on how injuries and losses are measured, or on when contract payments fall due. Assumed about it:
  - every wrong creates a debt (strict liability, above);
  - debts arise only from your own wrongs and your own valid contracts (`debt_requires_source`);
  - once a debt arising from wrongs is paid off, it stays paid off unless the debtor wrongs the same person again (`paid_stays_paid`). Contract debts are exempt, since installments fall due repeatedly.
- **Compensates** (`CompensatesAt`). Which of a debtor's possessions are designated as payment at a given time. Also undefined. It could reflect market value, the victim's subjective loss, a multiple of the loss, the contract's terms, or anything else. Assumed about it: a single thing pays only one creditor at a time, and the first-in-time rule above.

- **Guardian** (`Guardian`) and **provides adequate care** (`Provides`). Who has custody of a dependent, and whether they are caring for them adequately. Both are deliberately left undefined. The model takes no side on how guardianship arises (birth, adoption or otherwise) or on what counts as adequate care.
- **Capable** (`Capable`). Whether someone is able to choose at a given time: not asleep, in a coma, too young, or otherwise lacking the capacity for responsible choice. Deliberately left undefined, so the model takes no side on ages, thresholds or degrees. Nothing is assumed about it.

The model does not require **necessity** (using no more force than needed). Proportionate force is permitted even if less force would have worked.

## How the moral words work

- **Permission and obligation** (`deontic_duality`). You are obliged to refrain from an act exactly when you are not permitted to do it.

## Definitions

These are not premises. They fix what the premises are about.

- **Neglect** (`Neglects`). A guardian neglects a dependent when they keep custody of them without providing adequate care.
- **Aggression** (`Aggressing`). Someone is aggressing in one of two ways:
  - they are trying to take something from its owner while the owner is holding it; or
  - they are neglecting a dependent in their custody. The book's analogy is a husband who locks his wife in the basement and lets her starve.
- **Entitled to enforce** (`EntitledToEnforce`). You may enforce someone's claim if you are that person, or if they haven't declined help from others *while having the capacity to choose*. Someone lacking capacity can't veto help, and no guardian can veto on their behalf.
- **Culpable** (`Culpable`). Someone is culpable for an act if they do it, it is forbidden, and they currently have the capacity to choose. This separates judging an *act* (permitted or forbidden) from judging the *person* (to blame or not).
- **Liable** (`Liable`). An aggressor is liable to a given use of force from a given person when that person is entitled to enforce the victim's claim and the force is proportionate to stopping the aggression.
- **Conflict** (`InConflict`). Two acts conflict when they physically can't both happen. Conflict is a matter of physical fact; who owns what plays no part in it.
  - Taking something from a person who holds it conflicts with that person using it, with that person defending it, and with anyone intervening to stop the taking.
  - Using a particular force on someone's body, whether to stop an aggression or otherwise, conflicts with that person resisting that force.
  - Two different people using the same scarce thing at the same time conflict.
  - Forcibly stopping someone's act conflicts with their doing it.

## Moral premises

These are the fields of `JurisdictionUPB`. They carry the argument's moral content.

- **P1, Compossibility** (`compossible`). In every physical conflict, at least one party is obliged to yield. In other words, two acts that physically conflict are never both permitted. Lean proves the two phrasings equivalent (`compossible_iff_decisive`). This is the book's point that a set of norms exists to settle conflicts, not to leave everyone "pointing guns at each other's faces."
- **P3a, Use** (`owner_use`). You may use what you own, unless you have currently lent it to someone else.
- **P3b, Defense** (`owner_defend`). You may resist anyone's attempt to take what you own, including your body.
- **P3d, Bodily resistance, with liability** (`body_resist`). You may resist force used against your body, with one exception: while you are aggressing, you may not count on resisting *proportionate* force from someone entitled to stop you. Against excessive force, an aggressor keeps the right to resist.
- **P3e, Licenses** (`licensed_use`). Someone the owner currently permits to use a thing may use it.
- **P4, Liberty** (`avoidable_perm`). Actions others can simply avoid are permitted.

The P5 premises express one principle of **standing**: a claim may be enforced by its owner and by anyone else unless the owner, while capable, declines, and by no one else. "Entitled to enforce" (defined above) captures exactly that group.

- **P5a, Enforcement: defense** (`enforce_defense`). Anyone entitled to enforce the victim's claim may use proportionate force to stop an ongoing aggression. With the victim as enforcer, this is self-defense.
- **P5b, Enforcement: recovery** (`enforce_recovery`). Anyone entitled to enforce the owner's claim may take the thing back from someone who holds it but neither owns it nor has the owner's permission to use it. A borrower isn't a thief. With the owner as enforcer, this is the owner recovering their own property.
- **P5c, Standing** (`standing`). Someone not entitled to enforce a claim may not enforce it, either by intervening or by taking the thing from anyone. This is the owner's veto, which only someone with the capacity to choose can exercise.

The numbering keeps the labels used throughout the discussion. There is no P2: the agent-symmetry premise of the original formalization was dropped (see `archive/UPBSymmetry.lean` for why). There is no longer a P3c: recovery by the owner is now the owner's case of P5b. The former P5c and P5d (the two vetoes) are now the single standing premise P5c.

## What follows from them

From these premises, Lean verifies the following. `Conclusions.md` gives each result in full, with its theorem name and what it rests on.

**Title**
- Every person owns their own body, no thing has two owners, and anyone holding something nobody else owns is its owner. Even apart from the physical facts, P1 and P3a rule out two people owning the same thing.
- Title depends only on the history: first possessions, transfers, wrongs and agreements. No decree, vote, uniform, self-written deed or act of force can create or transfer it.
- The only ways to gain title are first possession, voluntary transfer from the owner, and payment of a debt the owner owes you. A thief can't pass on title by selling stolen goods, and no one can consent, contract or vote away your property on your behalf.
- Fraud, duress and lack of capacity pass no title: whoever handed something over in those circumstances still owns it and may take it back.

**Bodies and property**
- No one may take control of another person's body, even an aggressor's, and that person may resist, including against confinement. Someone who is not aggressing may resist any force used against their body.
- No one may assault or murder a peaceful person, and the victim may resist. Consensual bodily contact, such as surgery, isn't assault.
- No one may take an owned thing from its owner while the owner holds it, whatever the taker's role or title. Something held by a person whom no one else has a claim against may not be taken from them.
- No one may use a thing they don't own without the owner's permission. Someone with permission may use it, and the owner yields while the permission lasts.

**Recovery, restitution and contracts**
- An owner may recover stolen property, and the thief may neither keep using it nor resist. Unless the owner, while capable, declines, anyone may recover it on the owner's behalf, and a rescuer must give it back. A borrower must return what they borrowed once permission ends.
- Taking, destroying or damaging what someone owns, or injuring them, is a wrong whatever the reason, so even stealing to survive creates a debt. The debt is paid from the wrongdoer's own property, including property acquired later. The victim owns what is designated as payment and may collect it, and earlier creditors come first.
- Valid contracts create debts collected in the same way, in the same first-in-time queue. Contracts obtained by fraud or duress, or made without capacity, create no debt. Only you can obligate yourself, and no debt or contract can transfer anyone's body.

**Defense and the use of force**
- Unless the victim, while capable, declines, anyone may use proportionate force to stop an ongoing aggression, and the aggressor may not resist it. Some permitted way of doing so always exists.
- Excessive force is forbidden, and the aggressor may resist it. This is derived, not assumed: it follows from P3d and P1.

**Liberty**
- No one may forcibly stop someone doing what they are permitted to do. This is derived from P1 alone. It covers avoidable acts such as rudeness, lateness or lying, and people using their own body or property, even in ways that harm or end their own life. This rules out enforcing laws against victimless crimes, and "practicality" is no exception.
- Freedom of association: no one may force anyone into association or stop them declining it.
- Harming yourself or your own property wrongs no one.

**Capacity and dependents**
- Consent requires capacity. Someone lacking the capacity to choose, such as a child, can make neither a voluntary transfer nor a valid contract, and can't veto help.
- No one is culpable for what they do while lacking capacity, but they may still be stopped with proportionate force, still owe restitution for harms, and keep all their rights.
- A guardian must provide or relinquish. Anyone may use proportionate force to remove a dependent from a guardian who keeps custody without providing care, the guardian may not resist, and neither the dependent nor the guardian can veto the rescue.

**No exemptions and consistency**
- No office, uniform, majority vote or claimed authority creates an exemption from any of these prohibitions.
- The premises are consistent: there is a rule system that satisfies all of them in every possible situation, and for every meaning of the undefined terms.
