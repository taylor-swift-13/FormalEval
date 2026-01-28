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

(* Helper function for efficient computation *)
Fixpoint fib4_iter (k : nat) (a b c d : nat) : nat :=
  match k with
  | 0 => a
  | S k' => fib4_iter k' b c d (a + b + c + d)
  end.

Definition fib4_calc (n : nat) : nat := fib4_iter n 0 0 2 0.

(* Proof of correctness for the helper function *)
Lemma fib4_iter_correct : forall k i a b c d,
  fib4_at i a ->
  fib4_at (S i) b ->
  fib4_at (S (S i)) c ->
  fib4_at (S (S (S i))) d ->
  fib4_at (i + k) (fib4_iter k a b c d).
Proof.
  induction k; intros.
  - simpl. rewrite Nat.add_0_r. assumption.
  - simpl. rewrite <- Nat.add_succ_comm.
    apply IHk.
    + assumption.
    + assumption.
    + assumption.
    + apply fib4_at_SSSS; assumption.
Qed.

Lemma fib4_calc_correct : forall n, fib4_at n (fib4_calc n).
Proof.
  intros. unfold fib4_calc.
  replace n with (0 + n) by apply Nat.add_0_l.
  apply fib4_iter_correct.
  - apply fib4_at_0.
  - apply fib4_at_1.
  - apply fib4_at_2.
  - apply fib4_at_3.
Qed.

(* Test case proof *)
Example test_fib4_23 : problem_46_spec 23 526768.
Proof.
  unfold problem_46_spec.
  replace 526768 with (fib4_calc 23) by reflexivity.
  apply fib4_calc_correct.
Qed.