Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(* Inductive relation definition for fib4 sequence *)
Inductive fib4_at : nat -> nat -> Prop :=
| fib4_at_0 : fib4_at 0 0
| fib4_at_1 : fib4_at 1 0
| fib4_at_2 : fib4_at 2 2
| fib4_at_3 : fib4_at 3 0
| fib4_at_SSSS : forall i a b c d,
    fib4_at i a ->
    fib4_at (S i) b ->
    fib4_at (S (S i)) c ->
    fib4_at (S (S (S i))) d ->
    fib4_at (S (S (S (S i)))) (a + b + c + d).

(* Pre-condition *)
Definition problem_46_pre (input : nat) : Prop := True.

(* Post-condition specification *)
Definition problem_46_spec (input : nat) (output : nat) : Prop :=
  fib4_at input output.

Fixpoint fib4_iter (k : nat) (a b c d : nat) : nat :=
  match k with
  | 0 => a
  | S k' => fib4_iter k' b c d (a + b + c + d)
  end.

Lemma fib4_iter_correct : forall k i a b c d,
  fib4_at i a ->
  fib4_at (S i) b ->
  fib4_at (S (S i)) c ->
  fib4_at (S (S (S i))) d ->
  fib4_at (i + k) (fib4_iter k a b c d).
Proof.
  induction k as [|k IH]; intros.
  - simpl. rewrite Nat.add_0_r. assumption.
  - simpl. apply IH.
    + assumption.
    + assumption.
    + assumption.
    + apply fib4_at_SSSS; assumption.
Qed.

Definition fib4_compute (n : nat) : nat :=
  fib4_iter n 0 0 2 0.

Lemma fib4_compute_correct : forall n, fib4_at n (fib4_compute n).
Proof.
  intros.
  unfold fib4_compute.
  replace n with (0 + n) by reflexivity.
  apply fib4_iter_correct.
  - apply fib4_at_0.
  - apply fib4_at_1.
  - apply fib4_at_2.
  - apply fib4_at_3.
Qed.

Example test_fib4_12 : problem_46_spec 12 386.
Proof.
  unfold problem_46_spec.
  replace 386 with (fib4_compute 12).
  - apply fib4_compute_correct.
  - reflexivity.
Qed.