Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint fib_iter (n : nat) (a b : Z) : Z :=
  match n with
  | O => a
  | S n' => fib_iter n' b (a + b)
  end.

Definition fib (n : Z) : Z :=
  match n with
  | Z0 => 0
  | Zpos p => fib_iter (Pos.to_nat p) 0 1
  | Zneg _ => 0
  end.

Definition problem_55_pre (n : Z) : Prop := True.

Definition problem_55_spec (n : Z) (res : Z) : Prop :=
  res = fib n.

Example problem_55_test : problem_55_spec 45 1134903170.
Proof.
  unfold problem_55_spec.
  vm_compute.
  reflexivity.
Qed.