# Conclusions of the Jurisdiction-Route Formalization

This note states, in plain English, what the theory in `UPBJurisdiction.lean` concludes. Each conclusion has been checked by Lean, the proof assistant: it follows from the premises listed in `Premises.md`, with no gaps. Whether the conclusions are *true* depends on whether those premises are, and `Limitations.md` lists what the model leaves out.

Each conclusion gives its theorem number and Lean name, and says what it rests on. Some conclusions are genuinely derived: they follow from combining premises and could not be read off any single one. Others mostly restate a premise in a particular setting. Both kinds are marked, so it's clear where the argument does real work.

Throughout, "may" means *is permitted to*, and "may not" means *is obliged to refrain from*.

## Title

These conclusions are about who owns what. They used to be premises. Now they follow from one principle, that title comes only from first possession or from an owner's voluntary transfer (P0), together with the premise that bodies can't be transferred (P0b) and physical facts.

**Every person owns their own body** (`World.self_sovereignty`).

- *Derived* from P0, P0b and the physical fact that each person was the first to possess their own body. Because a body can't be transferred, that title is never lost.

**No thing has two owners** (`World.exclusive_jurisdiction`).

- *Derived* from P0 and two physical facts: a thing has only one first possessor, and no one can hand the same thing to two people at once. The proof follows title step by step through time.

**The moral premises alone also rule out two owners** (Theorem 0, `premises_force_exclusivity`). Even without the physical facts about first possession, if two people owned the same thing, each would be permitted to use it. Their uses would physically conflict, and compossibility (P1) forbids permitting both.

- *Derived* from P1, owners' use (P3a), and the fact that two people can't use one scarce thing at once. This shows exclusivity is not an extra assumption the theory needs; the theory's core commitments already require it.

**If you hold something and nobody else owns it, it is yours** (`World.acquisition`).

- *Derived*: whatever is held was first possessed by someone. Title is never lost, only kept or passed on, so someone owns it now.

**No decree, vote, uniform or act of force can create or transfer title** (`World.title_depends_only_on_history`). Two situations with the same history of first possessions and voluntary transfers agree on who owns what, however they differ otherwise. That includes who currently holds what, so stealing something does not make it the thief's. It also includes any declaration, election or office, none of which is a first possession or an owner's voluntary transfer. And it includes a self-written deed: the book's would-be tax collector, with "a handwritten note saying that you own the whole neighbourhood," owns nothing by it.

- *Derived* directly from P0.

**No one can give what they don't own** (`History.only_ways_to_gain_title`). The only ways to gain title are to become a thing's first possessor, or to receive it voluntarily from someone who owns it. If a thief sells a stolen bike, the buyer gets no title; the original owner still owns it and may recover it from the buyer (Theorem 3B).

- *Derived* directly from P0.

**No one can consent or sign a contract on your behalf** (`History.others_cannot_transfer_your_title`). You keep title to what you own unless it passes from *you*, by your own voluntary transfer or to pay your own debt. Nothing anyone else does, signs, agrees to or votes for can transfer your property. That includes your parents, which answers the book's point that "I cannot sign a contract on your behalf, or on my children's behalf."

- *Derived* directly from P0.

**Fraud and duress pass no title** (`History.invalid_transfer_keeps_title`, `World.fraud_or_duress_victim_keeps_title`). If someone hands something over because they were deceived, or under threat of initiated force, they still own it afterwards, and the recipient doesn't.

- *Derived* from P0, whose notion of a voluntary transfer excludes deception and duress, and from the physical fact that no one can hand the same thing to two people at once.

## Bodies

**No one may take control of another person's body, and that person may resist** (Theorem 2, `bodily_non_aggression`). This covers kidnapping, enslavement, and any other seizing of control over someone's body. It holds for everyone, including aggressors. Stopping an aggressor is a different act (intervention with proportionate force, below); taking control of them is still forbidden. Confinement is a case: the book's wife locked in the basement may resist. By contrast, a wife whose husband is merely unfaithful hasn't had her body taken control of, and can simply leave.

- *Derived* from self-ownership, the right to resist takings (P3b), and compossibility (P1). Because the owner may resist, and taking and resisting can't both be permitted, the taking is forbidden.

**A person who is not aggressing may resist any force used against their body** (Theorem 2A, `peaceful_may_resist`). No one, whatever their reason, can use force against a peaceful person's body in a way that person must accept.

- *Mostly restates* P3d: a peaceful person is never liable, so the exception in P3d never applies to them.

## Property

**No one may take an owned thing from its owner while the owner holds it, and the owner may use it unless they've lent it out** (Theorems 1 and 3, `no_take_from_owner`, `property_non_aggression`). This is the prohibition of theft and robbery.

- *Derived*, in the same way as Theorem 2.

**No one may use a thing they don't own without the owner's permission** (Theorem 3F, `no_trespass`). This is the prohibition of trespass and unauthorized use.

- *Derived* from P1, P3a and P3e. If the owner has lent the thing to someone, that person's use conflicts with the trespasser's. Otherwise the owner's own use does. Either way, P1 forbids the trespass.

**Someone with the owner's permission may use the thing, and the owner yields while the permission lasts** (Theorem 3G, `licensed_use_and_owner_yields`). Lending, renting and inviting a guest all work this way.

- The borrower's permission *restates* P3e. The owner's obligation to yield is *derived* from P1, since both can't use the thing at once.

**Something you hold may not be taken from you if no one else has a claim to it** (Theorem 3A, `no_take_from_sole_claimant`). If you picked up a wild apple and no one else owns it, it's yours, and no one may take it from you.

- *Derived* from P0 plus Theorem 1: whatever you hold was first possessed by someone, and if no one else owns it, that someone must be you. This is the case the original formalization handled with its symmetry premise (P2). Here P2 isn't needed.

## Recovering stolen property

**An owner may take back stolen property, and the thief may neither keep using it nor resist** (Theorem 3B, `recovery`). This applies to anyone holding the owner's property without permission. A borrower isn't a thief: the rules on recovery don't apply while a loan lasts.

- The owner's permission *restates* P5b, with the owner as the enforcer.
- The thief's obligations are *derived*: since the owner may take it back, and the thief's use or resistance would physically conflict with that, P1 forbids the thief's use and resistance.

**Unless the owner declines, anyone may take stolen property back from the thief on the owner's behalf, and the thief may neither keep using it nor resist** (Theorem 3C, `third_party_recovery`).

- The rescuer's permission *restates* P5b, with someone the owner hasn't excluded as the enforcer. The thief's obligations are *derived*, as in 3B.

**A rescuer must give recovered property back** (Theorem 3D, `rescuer_must_return`). Once the rescuer holds it, the owner may take it from them, and the rescuer may neither keep using it nor resist.

- *Derived*: this is Theorem 3B applied to the rescuer. No separate premise about returning property was needed.

**If the owner declines, while having the capacity to choose, no one else may take the property on their behalf** (Theorem 3E, `vetoed_recovery`).

- *Restates* the standing premise P5c: once the owner declines, no one else is entitled to enforce their claim.

**A borrower must return what they borrowed, and owes for any damage** (Theorem 3J, `borrower_must_return`). Once the owner's permission ends, the owner may take the thing back, and the borrower may neither keep using it nor resist. Damaging it while borrowed is a wrong (`History.destruction_wrongs`), so it creates a debt. The book: "if I borrow your lawnmower, I am obligated to bring it back in more or less the same state."

- *Derived*: once permission ends, Theorem 3B applies.

**Victims of fraud or duress may take back what they handed over** (Theorem 3H, `fraud_or_duress_recovery`). The recipient may neither keep using it nor resist.

- *Derived*: the victim still owns it (see *Title*), so Theorem 3B applies.
- This settles an inconsistency in the book. Its text treats fraud as avoidable, while Appendix B lists it as enforceable. Here, fraud that obtains property is enforceable through recovery. A lie that obtains nothing is an avoidable act, which may not be stopped by force (Theorem 7A).

## Restitution

These results cover compensation for wrongs, when returning the thing itself isn't enough: the thing was destroyed, or someone was injured. Liability is strict. Taking or damaging what someone owns, or injuring them, is a wrong whatever the reason.

**Destroying or damaging what someone else owns wrongs them, whatever the reason** (`History.destruction_wrongs`). The book's lifeboat example is a case: breaking a stranger's window to save your own life is still a wrong, though an understandable one.

- *Restates* the strict-liability definition of a wrong in P0.

**Taking what someone else owns wrongs them, whatever the reason** (`History.taking_wrongs`). The book's starving man who steals an apple does wrong, though understandably, and "must justly accept the consequences": he owes restitution.

- *Restates* the strict-liability definition of a wrong in P0.

**Every wrong creates a debt to the victim** (`World.debt_after_wrong`). The debt stays owed until it is paid off.

- *Restates* the strict-liability part of P0.

**A victim owns the compensation designated for a debt owed to them** (`World.restitution_owned`). While someone owes you, whatever of their transferable property is designated as compensation becomes yours, and stops being theirs. **Debts don't lapse:** the property can be something the wrongdoer acquired long after the wrong. A thief who was penniless at the time still owes you out of what they earn later.

- *Derived* from P0. Only the wrongdoer's own property can pass, never anyone else's. Family, employers and taxpayers owe nothing.
- How much is owed, and when a debt counts as paid, are left open. "Still owed" and "compensates" are undefined terms, so the model needs no unit of value.

**Earlier victims come first** (`World.earlier_victims_first`). While a victim with an older claim is still owed, none of the wrongdoer's property can go to a later victim. A victim's claim also takes priority over a gift the wrongdoer makes at the same moment.

- *Restates* the first-in-time part of P0.

**No one's body can be taken as compensation** (`World.no_restitution_from_body`). Restitution comes from property only. There is no compelled labor or servitude to pay off a debt.

- *Derived* from P0b, since bodies can't be transferred.

**A victim may collect their compensation, and the wrongdoer may neither keep using it nor resist** (Theorem 3I, `restitution_collection`). Unless the victim declines, others may collect on their behalf (Theorem 3C). Any force against the wrongdoer's body must be proportionate.

- *Derived*: the victim owns the compensation, so the recovery results (3B, 3C) apply unchanged.

**A victim may forgive a debt.** No separate rule is needed: a victim who has received compensation owns it, and may give it back like anything else they own.

## Contracts

Contracts follow the title-transfer theory. A valid contract creates a debt, exactly as a wrong does, so every result about restitution above also applies to contract debts.

**Contract debts can be collected** (Theorem 3I, `restitution_collection`). When a payment under a contract is due, property designated as payment belongs to the creditor, who may take it; the debtor may neither keep using it nor resist. This covers repaying a loan, paying for a meal and forfeiting a deposit. Others may collect on the creditor's behalf unless the creditor declines.

- *Derived*: a contract debt is treated like any other debt (see *Restitution*).

**Victims of wrongs and contract creditors share one queue** (`World.earlier_victims_first`). Whoever's claim is older is paid first, whether it arose from a wrong or a contract.

- *Restates* the first-in-time part of P0.

**A contract obtained by fraud or duress isn't valid** (`World.invalid_agreement`), **and only you can obligate yourself** (`World.no_debt_without_source`). If you have neither wronged someone nor validly agreed to a contract with them, you owe them nothing. A contract your parents, a representative or "society" agreed to in your name creates no debt for you.

- *Derived* from P0 and the assumption that debts arise only from your own wrongs and valid contracts.

**No contract can transfer your body** (`World.no_restitution_from_body`). A contract to subject yourself to someone else's control for life transfers nothing. This matches the book's *Practicality* conclusion, reached here through P0b rather than the book's competence argument. A promise to *work* isn't enforceable as such; only a stipulated forfeiture of property is.

- *Derived* from P0b.

**Breaking a contract is not a further wrong.** Any penalty for breach must be part of the contract itself, such as a deposit forfeited on failure.

- This is a design choice in P0, not a derived result.

## Moral capacity

These results separate judging an *act* (permitted or forbidden) from judging the *person* who does it (to blame or not). Whether someone has the capacity to choose is an undefined term: the model takes no side on ages, thresholds or degrees.

**Consent requires capacity** (`History.consent_requires_capacity`). Someone lacking the capacity to choose, such as a young child or a sleepwalker, can make neither a voluntary transfer nor a valid contract. This gives the book's "children cannot enter into legal contracts."

- *Derived* directly from P0's definitions of a voluntary transfer and a valid contract.

**A handover by someone lacking capacity passes no title** (`History.incapable_transfer_keeps_title`). If a child hands over their bike, it's still theirs.

- *Derived* from P0.

**No one is to blame for what they do while lacking capacity** (Theorem 12, `no_culpability_without_capacity`). A sleepwalker who steals isn't evil, even though stealing is forbidden.

- *Derived* directly from the definition of culpability.

**Someone attacking while lacking capacity may still be stopped** (Theorem 12A, `incapable_aggressor_may_be_stopped`). A sleepwalker or confused person may be stopped with proportionate force and may not resist. This is the book's "although we may restrain him."

- *Derived*: this is Theorem 6. Liability to defensive force depends on what someone is doing, not on their state of mind.

**Harms done while lacking capacity still create a debt.** The sleepwalker who breaks a window owes for it, just as in the lifeboat case.

- This follows from strict liability: the definition of a wrong doesn't mention capacity. Being blameless doesn't cancel the debt.

**Those lacking capacity keep their rights** (Theorem 12B, `incapable_keep_rights`). Children and people in comas can't be culpable, but they can be wronged. No one may take control of their bodies, and they keep title to them.

- *Derived* from Theorem 2 and self-ownership, neither of which depends on capacity.

## Parents and children

These results give the book's conclusion that parents must feed their children or hand them over to someone who will. The duty is **provide or relinquish**: the wrong isn't failing to feed in itself, but keeping a dependent in your custody without providing for them. Enforcement means removing the child, not forcing the parent to work.

**Neglect in custody is aggression** (`World.Aggressing`). A guardian who keeps custody of a dependent without providing adequate care is aggressing against them, so every result about defense applies.

- This is a definition. It is the book's own analogy: children are "the moral equivalent of kidnap victims," and neglect is like locking someone in the basement and letting them starve.

**A guardian can end the aggression by providing care or by giving up custody** (`World.provide_or_relinquish`).

- *Derived* from the definition.

**Anyone may rescue a neglected child, and the guardian may not resist** (Theorem 13, `rescue_from_neglect`). Proportionate force may be used to remove the child. Some permitted way to do so always exists (Theorem 13A, `rescue_available`).

- *Derived* from the defense results (Theorems 6 and 6A). The child, lacking capacity, can't veto the rescue (`World.anyone_may_help_incapable`), and the guardian has no veto on the child's behalf.
- Nothing here is specific to children. It covers anyone in custody who lacks capacity, such as the residents of the book's nursing home.

**A guardian can't give away a child's property or bind the child to a contract.** A child can receive gifts. A guardian's powers go no further than that, so neither the guardian nor anyone else can dispose of what the child owns, or agree to anything in the child's name.

- *Derived* from consent requiring capacity (`consent_requires_capacity`) and only you being able to obligate yourself (`no_debt_without_source`, `others_cannot_transfer_your_title`).

**Compulsory schooling.** Forcing a child to attend school is taking control of the child's body, which Theorem 2 forbids. Funding schools through taxes falls under the taxation analysis below.

## Defense and the use of force

**Unless the victim declines, anyone may use proportionate force to stop an ongoing aggression, and the aggressor may not resist it** (Theorem 6, `defense_of_others`). When the defender is the victim, this is self-defense, and the victim needs no one's permission.

- The defender's permission *restates* P5a.
- The aggressor's obligation not to resist is *derived* from P1, since the defense and the resistance physically conflict.

**Whenever an aggression is under way, anyone entitled to stop it has some permitted way of doing so** (Theorem 6A, `defense_available`). The right of defense is never empty.

- *Derived* from P5a and the assumption that some proportionate force always exists.

**Excessive force is forbidden, and the aggressor may resist it** (Theorem 6B, `excessive_force_forbidden`). If a use of force is not proportionate to stopping the aggression, the defender may not use it, even against an aggressor, and the aggressor may fight back against it.

- *Derived*, and one of the more substantive results. No premise says excessive force is forbidden. It follows because an aggressor keeps the right to resist force they aren't liable to (P3d), and P1 rules out permitting both that resistance and the excessive force.

**If the victim declines, while having the capacity to choose, no one else may intervene on their behalf, with any amount of force** (Theorem 6C, `vetoed_defense`).

- *Restates* the standing premise P5c, as in 3E.

**What counts as proportionate is left open.** "Proportionate" is an undefined term, so the theory never says whether a particular use of force, such as lethal force against a mugger, is proportionate. It says only what follows either way: proportionate force is permitted and may not be resisted, and excessive force is forbidden and may be resisted. Necessity is not required: proportionate force is permitted even if less would have worked.

## Assault and murder

**No one may use force against the body of someone who is not liable to it, and the victim may resist** (Theorem 9, `no_assault`). In particular, no one may use any force, lethal or not, against a peaceful person (Theorem 9A, `no_assault_on_peaceful`). This is the prohibition of assault, and of murder when the force is lethal.

- *Derived* from bodily resistance (P3d) and P1. The victim may resist force they aren't liable to, the attack and the resistance physically conflict, and P1 forbids permitting both.
- Lethal force *in defense* is still permitted when it is proportionate (Theorem 6). The model leaves open whether lethal force is ever proportionate.

**Consensual bodily contact isn't assault** (Theorem 3K, `consensual_bodily_contact`). Someone who permits another to use their body, like a patient consenting to surgery, makes that use permitted. The book's surgeon "stabs" you with a scalpel, but by your consent, unlike the mugger.

- *Derived* from licenses (P3e), applied to the body.

## Forcibly stopping what others may do

**No one may use force to stop someone else from doing what they are permitted to do** (Theorem 7, `no_stopping_permitted_acts`).

- *Derived* from P1 alone: forcibly stopping an act physically conflicts with doing it. This is a general principle; the next two results are special cases.
- Stopping an *aggression* is a different matter. It is covered by the rules on defense above, because aggression isn't permitted.

**No one may use force to stop someone else's avoidable act** (Theorem 7A, `no_force_against_avoidable`). An avoidable act is one that crosses no one's boundary and that others can simply avoid, such as rudeness, lateness, lying, or bad taste. You may dislike it and you may stay away from the person, but you may not use force to stop it.

- *Derived* from P4 (avoidable acts are permitted) and Theorem 7. This is the line the book draws between ethics (what may be enforced) and aesthetics (what may not).

**No one may use force to stop people using their own body or property** (Theorem 7B, `no_victimless_crime_enforcement`). For example, no one may forcibly stop a person from taking drugs, whatever the law says. With Theorem 8 below, this applies to police and officials as much as to anyone else.

- *Derived* from owners' use (P3a) and Theorem 7.

**No one may forcibly stop someone using their own body as they choose, even in ways that harm or end their own life** (Theorem 10, `no_stopping_self_harm`). The book: "It is no crime to commit suicide, any more than it is to set fire to your own house."

- *Derived*: this is Theorem 7B applied to your own body.

**Harming yourself or your own property wrongs no one** (`History.no_wrong_to_oneself`). It creates no debt.

- *Derived* directly from the definition of a wrong, which requires a victim other than the wrongdoer.

**Freedom of association** (Theorem 11, `freedom_of_association`). No one may forcibly stop someone declining to associate with them, whether that means refusing to trade, befriend, employ or attend a school. No one may take control of a person's body to force them into association.

- *Derived* from Theorems 7A and 2.

**"Practicality" doesn't justify force.** No one may forcibly stop a permitted act, even if forcing people to act "more practically" would be better for them. This is Theorem 7, and answers the book's *Practicality* section.

## No exemptions

**No role, office or majority creates an exemption** (Theorem 8, `no_role_exemption`). Take any property of people at all: holding an office, wearing a uniform, being in the majority of a vote. Everyone with that property is bound by the same prohibitions as everyone else:
- they may not take an owned thing from its owner who holds it;
- they may not strike or kill a peaceful person;
- they may not forcibly stop anyone doing what they are permitted to do.

This covers the book's soldier, uniform, policeman and majority-vote examples. It also covers authority claimed from God, "the government" or "the majority": a claimed command is just another role, and grants nothing. In "Bob and Doug outvote Jane," the vote changes neither who owns what nor what anyone may do.

- *Restates* Theorems 1, 7 and 9A. The role plays no part in the proof, because no premise grants anything on the basis of who someone is. That is the point of the theorem: the premises give no foothold for an exemption.

**No one may take an owned thing from its owner, whatever their role, title, or office** (Theorem 4, `no_exemption`). A badge, an election, or a majority vote creates no permission that other people lack.

- *Restates* Theorem 1. Theorem 1 already covers every agent, so no feature of the taker can make a difference.
- What gives it teeth is that title depends only on the history of first possessions and owners' voluntary transfers (see *Title* above). An institution can't make itself the owner of someone's property by decree, election or vote, so its taking remains a taking from the owner, which Theorem 1 forbids.
- Applied to taxation: a tax collector gains title to the money only if its owner voluntarily gave it.
  - If the collector takes it by force, that is a taking from its owner, which Theorem 1 forbids.
  - If the owner hands it over under threat of initiated force, no title passes, and the payer may take it back (Theorem 3H).
  - Now that contracts are modeled, the social-contract position can be stated precisely. If each taxpayer had validly agreed to pay, taxes would be contract debts, and collecting them would be permitted like collecting any other debt (Theorem 3I). So the whole question becomes whether each taxpayer **validly agreed**:
    - **Did they agree at all?** For example, does living in a country, voting or using roads count as agreement by conduct? The model records agreements, including agreements by conduct, but doesn't decide what conduct counts.
    - **Was the agreement valid?** An agreement made under threat of initiated force isn't valid. If "agreeing" consists of staying where you live, and the alternative is being fined or imprisoned, the agreement is made under threat, provided the threat is of *initiated* force. Whether it is depends on whether the state had title to impose those conditions in the first place, and title can't come from decree (`title_depends_only_on_history`).
    - **Did they agree for themselves?** Only you can obligate yourself, so an agreement made by earlier generations or "the people" binds no one else (`no_debt_without_source`).
  - The formalization doesn't settle the first question, but it shows that the defender needs a yes to all three, and that the third rules out the most common inherited versions of the social contract.

## Consistency

**All the premises can hold together** (Theorem 5, `consistent`). For every possible situation, and every meaning of "proportionate", there is a rule system that satisfies every premise at once. The theory is therefore not contradictory, and its conclusions are not empty consequences of contradictory assumptions.

A worked example (`bystander_example`) applies the theory to an assault. With force measured on a scale and, for illustration only, force of level 1 or less counting as proportionate:

- a bystander may use force at level 1 to stop the assailant, and the assailant may not resist;
- the bystander may not use force at level 5, and the assailant may resist it.

## Summary

Taken together, the theory concludes the following:

- **Self-ownership and property.** Everyone owns their own body, which can't be transferred. People own what they first possessed or were voluntarily given by its owner. Title can't be created or transferred by decree, vote, force, fraud or threat, and a non-owner can't pass it on.
- **Use of property.** No one may use another's property without permission. Someone with permission may use it while the owner yields.
- **Non-aggression.** Taking control of another person's body or property is forbidden, for everyone, without exception, and so is assault or murder of a peaceful person. A peaceful person may resist any force used against them.
- **No forcible prevention.** No one may forcibly stop others doing what they are permitted to do, including using their own body and property, even to harm or end their own life, and even "for their own good." This rules out enforcing laws against victimless crimes.
- **Freedom of association.** No one may force anyone into association or stop them declining it.
- **No consent by proxy.** No one can consent, contract or vote away your property on your behalf.
- **No exemptions.** No office, uniform or majority vote creates an exemption from any of this.
- **Owner's rights.** Owners may use, defend and recover what they own.
- **Defense and recovery by others.** Anyone may defend victims and recover stolen property on their behalf, unless the victim or owner declines. Victims of fraud or duress may take back what they handed over.
- **Restitution.** Whoever takes, destroys or damages what someone owns, or injures them, owes compensation from their own property, under strict liability, until the debt is paid off. The victim owns what is designated as compensation and may collect it. Earlier victims come first, debts don't lapse, and no one's body can be taken.
- **Contracts.** Valid contracts create debts that can be collected the same way, in the same queue. Contracts obtained by fraud or duress create no debt, only you can obligate yourself, and no contract can transfer your body.
- **Moral capacity.** Consent requires the capacity to choose. No one is to blame for what they do without it, but they may still be stopped, still owe restitution for harms, and keep all their rights.
- **Parents and children.** A guardian must provide or relinquish. Anyone may rescue a neglected child, and the guardian may not resist. Neither the child nor the guardian can veto the rescue, and a guardian can't dispose of the child's property or bind the child to contracts.
- **Limits on defensive force.** Defensive force must be proportionate. Excessive force is itself forbidden and may be resisted.
- **No force against avoidable acts.** Rudeness, lateness, lying and other acts others can simply avoid may not be stopped by force.
- **No resistance by wrongdoers.** Aggressors and thieves may not resist legitimate defense or recovery.

None of this relies on agent symmetry. It rests on title from first possession and consensual transfer, the principle that every conflict has a party who must yield, owners' standing, a single principle of who may enforce a claim, the liberty of avoidable acts, and a requirement of proportionate force whose content is left open.
