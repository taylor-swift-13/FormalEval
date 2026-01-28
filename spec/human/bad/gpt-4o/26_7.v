Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.
Import ListNotations.
Local Open Scope Z_scope.

Definition problem_26_pre (input : list Z): Prop := True.

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

Example test_case_1 :
  problem_26_spec [2%Z; 2%Z; 2%Z; 2%Z] [].
Proof.
  unfold problem_26_spec.
  split.
  - intros j v H. destruct j; inversion H.
  - split.
    + intros i v H H_unique. exfalso. 
      apply (H_unique i); assumption.
    + intros j1 j2 v1 v2 H1 H2 H_order. destruct j1; destruct j2; inversion H1; inversion H2; auto.
Qed.