Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Fixpoint fib_z (n : nat) : Z :=
  match n with
  | 0%nat => 0
  | S n' => match n' with
    | 0%nat => 1
    | S n'' => fib_z n'' + fib_z n'
    end
  end.

Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec (n : nat) (res : Z) : Prop :=
  res = fib_z n.

Example test_fib_62 : problem_55_spec 62%nat 4052739537881.
Proof.
  unfold problem_55_spec.
  native_compute.
  reflexivity.
Qed.