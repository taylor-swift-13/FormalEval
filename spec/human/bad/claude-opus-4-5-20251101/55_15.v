Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.

Fixpoint fib (n : nat) : Z :=
  match n with
  | 0 => 0%Z
  | S n' => match n' with
    | 0 => 1%Z
    | S n'' => (fib n'' + fib n')%Z
    end
  end.

Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec (n : nat) (res : Z) : Prop :=
  res = fib n.

Example test_fib_64 : problem_55_spec 64 10610209857723%Z.
Proof.
  unfold problem_55_spec.
  native_compute.
  reflexivity.
Qed.