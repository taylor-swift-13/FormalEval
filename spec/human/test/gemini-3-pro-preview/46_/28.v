Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

(* Inductive relation definition for fib4 sequence *)
(* Modified to use Z for the output value to handle large numbers *)
Inductive fib4_at : nat -> Z -> Prop :=
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
Definition problem_46_spec (input : nat) (output : Z) : Prop :=
  fib4_at input output.

(* Helper function to compute fib4 efficiently *)
Fixpoint fib4_iter (n : nat) (a b c d : Z) : Z :=
  match n with
  | O => a
  | S n' => fib4_iter n' b c d (a + b + c + d)
  end.

Definition fib4_func (n : nat) : Z :=
  fib4_iter n 0 0 2 0.

(* Proof of correctness for the helper function *)
Lemma fib4_iter_correct : forall n i a b c d,
  fib4_at i a ->
  fib4_at (S i) b ->
  fib4_at (S (S i)) c ->
  fib4_at (S (S (S i))) d ->
  fib4_at (i + n)%nat (fib4_iter n a b c d).
Proof.
  induction n as [|n IH].
  - intros. simpl. rewrite Nat.add_0_r. assumption.
  - intros. simpl.
    replace ((i + S n)%nat) with ((S i + n)%nat).
    + apply IH.
      * assumption.
      * assumption.
      * assumption.
      * apply fib4_at_SSSS; assumption.
    + rewrite Nat.add_succ_r. rewrite Nat.add_succ_l. reflexivity.
Qed.

Lemma fib4_correct : forall n, fib4_at n (fib4_func n).
Proof.
  intros. unfold fib4_func.
  replace n with (0 + n)%nat by reflexivity.
  apply fib4_iter_correct.
  - apply fib4_at_0.
  - apply fib4_at_1.
  - apply fib4_at_2.
  - apply fib4_at_3.
Qed.

(* Test case proof *)
Example test_fib4_98 : problem_46_spec 98 1250966502919879120640717716.
Proof.
  unfold problem_46_spec.
  replace 1250966502919879120640717716 with (fib4_func 98).
  - apply fib4_correct.
  - vm_compute. reflexivity.
Qed.