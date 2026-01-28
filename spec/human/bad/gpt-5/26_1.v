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

Example problem_26_example_empty : problem_26_spec [] [].
Proof.
  unfold problem_26_spec.
  split.
  - intros j v Hnth. simpl in Hnth. inversion Hnth.
  - split.
    + intros i v Hi Huniq. simpl in Hi. inversion Hi.
    + intros j1 j2 v1 v2 H1 H2 Hj12. simpl in H1. inversion H1.
Qed.