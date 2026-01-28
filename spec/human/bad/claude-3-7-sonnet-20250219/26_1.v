Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.
Require Import Lia.
Import ListNotations.
Local Open Scope Z_scope.

Definition problem_26_spec (input : list Z) (output : list Z) : Prop :=
  (*  1: output 中的每个元素 v 都存在于 input 中，
     并且 v 在 input 中是唯一的。 *)
  (forall (j : nat) (v : Z),
     nth_error output j = Some v ->
     (exists i : nat,
        nth_error input i = Some v /\
        (forall k : nat, nth_error input k = Some v -> k = i))) /\

  (*  2: input 中任何只出现一次的元素，也必须出现在 output 中。 *)
  (forall (i : nat) (v : Z),
     nth_error input i = Some v ->
     (forall k : nat, nth_error input k = Some v -> k = i) ->
     In v output) /\

  (*  3: output 中元素的相对顺序与它们在 input 中的相对顺序保持一致。 *)
  (forall (j1 j2 : nat) (v1 v2 : Z),
     nth_error output j1 = Some v1 ->
     nth_error output j2 = Some v2 ->
     (j1 < j2)%nat ->
     (exists i1 i2 : nat,
        nth_error input i1 = Some v1 /\
        nth_error input i2 = Some v2 /\
        (i1 < i2)%nat)).

Example problem_26_spec_test_empty :
  problem_26_spec [] [].
Proof.
  unfold problem_26_spec.
  repeat split.
  - (* 1: output elements from input uniquely *)
    intros j v H.
    (* nth_error [] j = None always *)
    discriminate H.
  - (* 2: unique input elements appear in output *)
    intros i v H Huniq.
    discriminate H.
  - (* 3: order preservation in output *)
    intros j1 j2 v1 v2 H1 H2 Hlt.
    discriminate H1.
Qed.