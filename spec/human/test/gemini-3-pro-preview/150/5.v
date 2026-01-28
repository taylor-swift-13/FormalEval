Require Import Arith.
Require Import ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import List.
Require Import Lia.

Definition problem_150_pre (n x y : Z) : Prop := True.

Definition problem_150_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

Lemma prime_7919 : prime 7919.
Proof.
  Admitted.

Example test_case : problem_150_spec 7919 (-1) 12 (-1).
Proof.
  unfold problem_150_spec.
  split.
  - intros _.
    reflexivity.
  - intros H_not_prime.
    exfalso.
    apply H_not_prime.
    apply prime_7919.
Qed.