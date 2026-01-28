Require Import Arith.
Require Import ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import List.
Require Import Lia.

Definition problem_150_pre (n x y : Z) : Prop := True.

Definition problem_150_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

Example test_case : problem_150_spec (-4)%Z (-3)%Z (-26)%Z (-26)%Z.
Proof.
  unfold problem_150_spec.
  split.
  - intros H.
    destruct H as [H1 _].
    lia.
  - intros _.
    reflexivity.
Qed.