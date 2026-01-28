Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
    | 0 => 1
    | S n'' => fib n'' + fib n'
    end
  end.

Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec (n : nat) (res : nat) : Prop :=
  res = fib n.

Definition fib_Z (n : Z) : Z :=
  Z.of_nat (fib (Z.to_nat n)).

Definition problem_55_spec_Z (n : Z) (res : Z) : Prop :=
  res = fib_Z n.

Example test_fib_70 : problem_55_spec_Z 70%Z 190392490709135%Z.
Proof.
  unfold problem_55_spec_Z.
  unfold fib_Z.
  simpl.
  reflexivity.
Qed.