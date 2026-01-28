Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [5; 5; 9; -3; -6; 2; 3; 8; 1; 1] [5; 5; 9; 2; 3; 8; 1; 1].
Proof.
  unfold get_positive_spec.
  split.
  - (* Part 1: Verify elements in result are in input and positive *)
    intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; split; [simpl; tauto | lia] | ]).
    contradiction.
  - (* Part 2: Verify positive elements in input are in result *)
    intros x HIn HPos.
    simpl in HIn.
    repeat (destruct HIn as [H | HIn]; [subst | ]).
    + (* x = 5 *)
      simpl; tauto.
    + (* x = 5 *)
      simpl; tauto.
    + (* x = 9 *)
      simpl; tauto.
    + (* x = -3 *)
      lia.
    + (* x = -6 *)
      lia.
    + (* x = 2 *)
      simpl; tauto.
    + (* x = 3 *)
      simpl; tauto.
    + (* x = 8 *)
      simpl; tauto.
    + (* x = 1 *)
      simpl; tauto.
    + (* x = 1 *)
      simpl; tauto.
    + (* Empty tail *)
      contradiction.
Qed.