Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint fib4_iter (n : nat) (a b c d : Z) : Z :=
  match n with
  | 0%nat => a
  | S n' => fib4_iter n' b c d (a + b + c + d)
  end.

Definition fib4 (n : Z) : Z :=
  fib4_iter (Z.to_nat n) 0 0 2 0.

Definition problem_46_pre (input : Z) : Prop := True.

Definition problem_46_spec (input : Z) (output : Z) : Prop :=
  output = fib4 input.

Example test_problem_46 : problem_46_spec 41 71083647136.
Proof.
  unfold problem_46_spec.
  vm_compute.
  reflexivity.
Qed.