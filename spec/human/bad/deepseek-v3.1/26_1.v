Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Compare_dec.
Import ListNotations.
Local Open Scope Z_scope.

(* Program specification *)
Definition problem_26_spec (input : list Z) (output : list Z) : Prop :=
  (forall (j : nat) (v : Z),
     nth_error output j = Some v ->
     (exists i : nat,
        nth_error input i = Some v /\
        (forall k : nat, nth_error input k = Some v -> k = i))) /\
  (forall (i : nat) (v : Z),
     nth_error input i = Some v ->
     (forall k : nat, nth_error input k = Some v -> k = i) ->
     In v output) /\
  (forall (j1 j2 : nat) (v1 v2 : Z),
     nth_error output j1 = Some v1 ->
     nth_error output j2 = Some v2 ->
     (j1 < j2)%nat ->
     (exists i1 i2 : nat,
        nth_error input i1 = Some v1 /\
        nth_error input i2 = Some v2 /\
        (i1 < i2)%nat)).

(* Test case: input = [], output = [] *)
Example test_empty_list : problem_26_spec [] [].
Proof.
  unfold problem_26_spec.
  split. {
    intros j v H.
    simpl in H.
    destruct j; discriminate H.
  }
  split. {
    intros i v H1 H2.
    simpl in H1.
    destruct i; discriminate H1.
  }
  intros j1 j2 v1 v2 H1 H2 H3.
  simpl in H1, H2.
  destruct j1; try discriminate H1.
  destruct j2; try discriminate H2.
  lia.
Qed.