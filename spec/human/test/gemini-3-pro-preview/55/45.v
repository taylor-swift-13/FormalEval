Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint fib_iter (n : nat) (a b : Z) : Z :=
  match n with
  | O => a
  | S n' => fib_iter n' b (a + b)
  end.

Definition fib (n : Z) : Z :=
  fib_iter (Z.to_nat n) 0 1.

Definition problem_55_pre (n : Z) : Prop := True.

Definition problem_55_spec (n : Z) (res : Z) : Prop :=
  res = fib n.

Example problem_55_test : problem_55_spec 60 1548008755920.
Proof.
  unfold problem_55_spec.
  vm_compute.
  reflexivity.
Qed.