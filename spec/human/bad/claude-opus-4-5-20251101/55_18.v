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

Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec (n : nat) (res : nat) : Prop :=
  res = fib n.

Fixpoint fib_Z (n : nat) : Z :=
  match n with
  | 0 => 0%Z
  | S n' => match n' with
    | 0 => 1%Z
    | S n'' => (fib_Z n'' + fib_Z n')%Z
    end
  end.

Definition problem_55_spec_Z (n : nat) (res : Z) : Prop :=
  res = fib_Z n.

Example test_fib_71 : problem_55_spec_Z 71 308061521170129%Z.
Proof.
  unfold problem_55_spec_Z.
  native_compute.
  reflexivity.
Qed.