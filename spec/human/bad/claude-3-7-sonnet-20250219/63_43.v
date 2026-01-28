Require Import Coq.Init.Nat.
Require Import ZArith.
Open Scope Z_scope.

Fixpoint fibfib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    match n' with
    | 0 => 0
    | S n'' =>
      match n'' with
      | 0 => 1
      | S n''' => fibfib n' + fibfib n'' + fibfib n'''
      end
    end
  end.

Definition problem_63_spec (n : nat) (res : Z) : Prop :=
  res = Z.of_nat (fibfib n).

Example test_fibfib_55 : problem_63_spec 55 65720971788709%Z.
Proof.
  unfold problem_63_spec.
  simpl.
  reflexivity.
Qed.