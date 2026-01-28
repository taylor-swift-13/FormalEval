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

Example test_fib_63 : problem_55_spec 63%nat 6557470319842.
Proof.
  unfold problem_55_spec.
  native_compute.
  reflexivity.
Qed.