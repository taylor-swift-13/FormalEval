Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Z_scope.

Fixpoint fibfib_Z (n : nat) : Z :=
  match n with
  | 0%nat => 0
  | S n' =>
    match n' with
    | 0%nat => 0
    | S n'' =>
      match n'' with
      | 0%nat => 1
      | S n''' => fibfib_Z n' + fibfib_Z n'' + fibfib_Z n'''
      end
    end
  end.

Definition problem_63_pre (n : nat) : Prop := True.

Definition problem_63_spec (n : nat) (res : Z) : Prop :=
  res = fibfib_Z n.

Example test_fibfib_59 : problem_63_spec 59%nat 752145307699165.
Proof.
  unfold problem_63_spec.
  native_compute.
  reflexivity.
Qed.