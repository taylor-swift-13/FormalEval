Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Z_scope.

Fixpoint fib4_aux (n : nat) (a b c d : Z) : Z :=
  match n with
  | 0%nat => a
  | S n' => fib4_aux n' b c d (a + b + c + d)
  end.

Definition fib4 (n : nat) : Z :=
  fib4_aux n 0 0 2 0.

Definition problem_46_pre (input : nat) : Prop := True.

Definition problem_46_spec (input : nat) (output : Z) : Prop :=
  output = fib4 input.

Lemma fib4_86_value : fib4 86%nat = 475494474730804082221384.
Proof.
  unfold fib4.
  native_compute.
  reflexivity.
Qed.

Example test_fib4_86 : problem_46_spec 86%nat 475494474730804082221384.
Proof.
  unfold problem_46_spec.
  apply fib4_86_value.
Qed.