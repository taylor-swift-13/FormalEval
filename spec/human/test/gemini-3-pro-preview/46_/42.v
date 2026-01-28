Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint fib4_iter (n : nat) (a b c d : Z) : Z :=
  match n with
  | O => a
  | S n' => fib4_iter n' b c d (a + b + c + d)
  end.

Definition fib4 (n : Z) : Z :=
  fib4_iter (Z.to_nat n) 0 0 2 0.

Definition fib4_at (n : Z) (res : Z) : Prop :=
  fib4 n = res.

Definition problem_46_pre (input : Z) : Prop := True.

Definition problem_46_spec (input : Z) (output : Z) : Prop :=
  fib4_at input output.

Example test_fib4_97 : problem_46_spec 97 648988991706202294407873694.
Proof.
  unfold problem_46_spec, fib4_at, fib4.
  vm_compute.
  reflexivity.
Qed.