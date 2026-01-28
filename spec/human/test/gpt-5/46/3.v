Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.

Fixpoint fib4 (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n1 =>
    match n1 with
    | 0 => 0
    | S n2 =>
      match n2 with
      | 0 => 2
      | S n3 =>
        match n3 with
        | 0 => 0
        | S n4 => fib4 n1 + fib4 n2 + fib4 n3 + fib4 n4
        end
      end
    end
  end.

Definition problem_46_pre (input : nat) : Prop := True.

Definition problem_46_spec (input : nat) (output : nat) : Prop :=
  output = fib4 input.

Example problem_46_test_nat : problem_46_spec 10%nat 104%nat.
Proof.
  unfold problem_46_spec.
  vm_compute.
  reflexivity.
Qed.

Example problem_46_test_Z : problem_46_spec (Z.to_nat 10%Z) (Z.to_nat 104%Z).
Proof.
  unfold problem_46_spec.
  vm_compute.
  reflexivity.
Qed.