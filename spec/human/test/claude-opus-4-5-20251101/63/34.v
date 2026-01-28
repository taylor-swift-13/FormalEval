Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.

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

Fixpoint fibfib_memo (n : nat) (a b c : Z) : Z :=
  match n with
  | 0%nat => a
  | S n' =>
    match n' with
    | 0%nat => b
    | S n'' =>
      match n'' with
      | 0%nat => c
      | S n''' => fibfib_memo n' b c (a + b + c)
      end
    end
  end.

Definition fibfib_fast (n : nat) : Z := fibfib_memo n 0 0 1.

Definition problem_63_pre (n : nat) : Prop := True.

Definition problem_63_spec (n : nat) (res : Z) : Prop :=
  res = fibfib_fast n.

Example test_fibfib_61 : problem_63_spec 61%nat 2544489349890656.
Proof.
  unfold problem_63_spec.
  unfold fibfib_fast.
  native_compute.
  reflexivity.
Qed.