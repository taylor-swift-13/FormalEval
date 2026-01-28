Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition fib4 (n : Z) : Z :=
  let fix loop (k : nat) (a b c d : Z) :=
    match k with
    | O => a
    | S k' => loop k' b c d (a + b + c + d)
    end
  in
  loop (Z.to_nat n) 0 0 2 0.

Definition problem_46_pre (input : Z) : Prop := True.

Definition problem_46_spec (input : Z) (output : Z) : Prop :=
  output = fib4 input.

Example test_problem_46 : problem_46_spec 79 4809357057697235769150.
Proof.
  unfold problem_46_spec.
  vm_compute.
  reflexivity.
Qed.