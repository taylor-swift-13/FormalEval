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
Fixpoint fib4_iter (n : nat) (a b c d : nat) : nat :=
  match n with
  | 0 => a
  | S n' => fib4_iter n' b c d (a + b + c + d)
  end.

(* Lemma proving correspondence between fib4_iter and fib4_at *)
Lemma fib4_iter_correct : forall k i a b c d,
  fib4_at i a ->
  fib4_at (S i) b ->
  fib4_at (S (S i)) c ->
  fib4_at (S (S (S i))) d ->
  fib4_at (i + k) (fib4_iter k a b c d).
Proof.
  induction k; intros.
  - rewrite Nat.add_0_r. assumption.
  - rewrite Nat.add_succ_r. rewrite <- Nat.add_succ_l.
    apply IHk; try assumption.
    apply fib4_at_SSSS; assumption.
Qed.

(* Test case proof *)
Example test_fib4_24 : problem_46_spec 24 1015378.
Proof.
  unfold problem_46_spec.
  replace 1015378 with (fib4_iter 24 0 0 2 0) by reflexivity.
  replace 24 with (0 + 24) by reflexivity.
  apply fib4_iter_correct.
  - apply fib4_at_0.
  - apply fib4_at_1.
  - apply fib4_at_2.
  - apply fib4_at_3.
Qed.