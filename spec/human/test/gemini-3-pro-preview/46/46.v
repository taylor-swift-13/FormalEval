Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.

Fixpoint fib4_iter (n : nat) (a b c d : Z) : Z :=
  match n with
  | 0 => a
  | S n' => fib4_iter n' b c d (Z.add (Z.add (Z.add a b) c) d)
  end.

Definition fib4 (n : nat) : Z :=
  fib4_iter n 0%Z 0%Z 2%Z 0%Z.

Definition problem_46_pre (input : nat) : Prop := True.

Definition problem_46_spec (input : nat) (output : Z) : Prop :=
  output = fib4 input.

Example test_problem_46 : problem_46_spec 95 174670928672918843046473740%Z.
Proof.
  unfold problem_46_spec.
  vm_compute.
  reflexivity.
Qed.