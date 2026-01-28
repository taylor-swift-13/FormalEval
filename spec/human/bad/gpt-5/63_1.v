Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Local Open Scope Z_scope.

Fixpoint fibfib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    match n' with
    | 0 => 0
    | S n'' =>
      match n'' with
      | 0 => 1
      | S n''' => fibfib n' + fibfib n'' + fibfib n'''
      end
    end
  end.

Definition problem_63_pre (n : nat) : Prop := True.

Definition problem_63_spec (n : nat) (res : nat) : Prop :=
  res = fibfib n.

Example problem_63_test_spec_nat : problem_63_spec 2%nat 1%nat.
Proof.
  unfold problem_63_spec.
  simpl.
  reflexivity.
Qed.

Example problem_63_test_Z : Z.of_nat (fibfib (Z.to_nat 2%Z)) = 1%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.