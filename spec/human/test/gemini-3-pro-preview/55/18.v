Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint fib_aux (n : nat) (a b : Z) : Z :=
  match n with
  | 0%nat => a
  | S n' => fib_aux n' b (a + b)
  end.

Definition fib (n : nat) : Z :=
  fib_aux n 0 1.

Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec (n : nat) (res : Z) : Prop :=
  res = fib n.

Example problem_55_test : problem_55_spec 71 308061521170129.
Proof.
  unfold problem_55_spec.
  vm_compute.
  reflexivity.
Qed.