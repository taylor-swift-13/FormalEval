Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition get_positive_spec (l: list R) (res: list R) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec 
  [-3; 0.5; -4; 2.5; 5; -2.2; 0.3470794389448922; -8; -4; -7; -10.5; 9.9; -10.5] 
  [0.5; 2.5; 5; 0.3470794389448922; 9.9].
Proof.
  unfold get_positive_spec.
  split.
  - (* Part 1: Verify elements in result are in input and positive *)
    intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [ subst; split; [ simpl; tauto | lra ] | ]).
    contradiction.
  - (* Part 2: Verify positive elements in input are in result *)
    intros x HIn HPos.
    simpl in HIn.
    repeat (destruct HIn as [HIn | HIn]; [ subst; try lra; try (simpl; tauto) | ]).
    contradiction.
Qed.