Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
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

Example test_problem_46 : problem_46_spec 82 34443880418283540493826.
Proof.
  vm_compute.
  reflexivity.
Qed.