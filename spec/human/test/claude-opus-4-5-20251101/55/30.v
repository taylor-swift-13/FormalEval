Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
    | 0 => 1
    | S n'' => fib n'' + fib n'
    end
  end.

Fixpoint fib_tail_aux (n : nat) (a b : Z) : Z :=
  match n with
  | 0 => a
  | S n' => fib_tail_aux n' b (a + b)
  end.

Definition fib_tail (n : nat) : Z := fib_tail_aux n 0 1.

Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec_Z (n : nat) (res : Z) : Prop :=
  res = fib_tail n.

Example test_fib_66 : problem_55_spec_Z 66 27777890035288%Z.
Proof.
  unfold problem_55_spec_Z.
  unfold fib_tail.
  native_compute.
  reflexivity.
Qed.