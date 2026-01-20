Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [12.377301343805572; 1.6651177816249232; -4.430953128389664; -3.4; 11.754416969860902; 5.6; 10.889126081885; 10.1; 12.377301343805572] 12.377301343805572.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove result is in the list *)
    simpl.
    left. reflexivity.
  - (* Part 2: Prove for all x in list, x <= result *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]].
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + contradiction.
Qed.