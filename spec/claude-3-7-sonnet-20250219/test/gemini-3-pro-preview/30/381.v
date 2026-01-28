Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [-1; -2; -5; 0; -9; -3; -3; -4; 6; 0; 6; 7; -9; 8; 10] [6; 6; 7; 8; 10].
Proof.
  unfold get_positive_spec.
  split.
  - (* Part 1: Verify elements in result are in input and positive *)
    intros x H.
    simpl in H.
    repeat destruct H as [H | H]; subst; split; try (simpl; tauto); try lia.
  - (* Part 2: Verify positive elements in input are in result *)
    intros x HIn HPos.
    simpl in HIn.
    repeat destruct HIn as [HIn | HIn]; subst; try lia; simpl; tauto.
Qed.