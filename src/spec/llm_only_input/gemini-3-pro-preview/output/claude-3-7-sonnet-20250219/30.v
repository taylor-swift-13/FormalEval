Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [-1; -2; 4; 5; 6] [4; 5; 6].
Proof.
  unfold get_positive_spec.
  split.
  - (* Part 1: Verify elements in result are in input and positive *)
    intros x H.
    simpl in H.
    (* Destruct the hypothesis for the result list [4; 5; 6] *)
    destruct H as [H | [H | [H | H]]]; subst.
    + (* x = 4 *)
      split.
      * simpl. auto 10. (* Check membership in input list *)
      * lia.
    + (* x = 5 *)
      split.
      * simpl. auto 10.
      * lia.
    + (* x = 6 *)
      split.
      * simpl. auto 10.
      * lia.
    + (* False case from end of list *)
      contradiction.
  - (* Part 2: Verify positive elements in input are in result *)
    intros x HIn HPos.
    simpl in HIn.
    (* Destruct the hypothesis for the input list [-1; -2; 4; 5; 6] *)
    destruct HIn as [H | [H | [H | [H | [H | H]]]]]; subst.
    + (* x = -1 *)
      lia. (* -1 > 0 is false *)
    + (* x = -2 *)
      lia. (* -2 > 0 is false *)
    + (* x = 4 *)
      simpl. auto.
    + (* x = 5 *)
      simpl. auto.
    + (* x = 6 *)
      simpl. auto.
    + (* False case from end of list *)
      contradiction.
Qed.