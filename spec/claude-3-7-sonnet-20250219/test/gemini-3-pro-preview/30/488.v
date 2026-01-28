Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [-2; 10; -4; 6; 0; 6; -7; 7; -9; 10; -3; -4; 1; 0] [10; 6; 6; 7; 10; 1].
Proof.
  unfold get_positive_spec.
  split.
  - (* Part 1: Verify elements in result are in input and positive *)
    intros x H.
    repeat (destruct H as [H|H]; [subst; split; [simpl; tauto | lia] | ]).
    contradiction.
  - (* Part 2: Verify positive elements in input are in result *)
    intros x HIn HPos.
    repeat (destruct HIn as [HIn|HIn]; [subst; try lia; simpl; tauto | ]).
    contradiction.
Qed.