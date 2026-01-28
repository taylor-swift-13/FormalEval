Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Fixpoint fib_Z (n : nat) : Z :=
  match n with
  | 0%nat => 0
  | S n' => match n' with
    | 0%nat => 1
    | S n'' => fib_Z n'' + fib_Z n'
    end
  end.

Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec (n : nat) (res : Z) : Prop :=
  res = fib_Z n.

Example test_fib_67 : problem_55_spec 67%nat 44945570212853.
Proof.
  unfold problem_55_spec.
  native_compute.
  reflexivity.
Qed.