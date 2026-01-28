Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Fixpoint fib4_aux (n : nat) (a b c d : Z) : Z :=
  match n with
  | O => a
  | S n' => fib4_aux n' b c d (a + b + c + d)
  end.

Definition fib4 (n : Z) : Z :=
  fib4_aux (Z.to_nat n) 0 0 2 0.

Definition problem_46_pre (input : Z) : Prop := True.

Definition problem_46_spec (input : Z) (output : Z) : Prop :=
  output = fib4 input.

Example test_problem_46 : problem_46_spec 83 66392714182364268855232.
Proof.
  unfold problem_46_spec.
  vm_compute.
  reflexivity.
Qed.