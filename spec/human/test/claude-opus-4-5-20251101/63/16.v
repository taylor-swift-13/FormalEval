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

Fixpoint fibfib_memo_aux (n : nat) (a b c : Z) : Z :=
  match n with
  | 0%nat => a
  | S n' => fibfib_memo_aux n' b c (a + b + c)
  end.

Definition fibfib_fast (n : nat) : Z :=
  fibfib_memo_aux n 0 0 1.

Definition problem_63_pre (n : nat) : Prop := True.

Definition problem_63_spec (n : nat) (res : Z) : Prop :=
  res = fibfib_fast n.

Example test_fibfib_57 : problem_63_spec 57%nat 222332455004452.
Proof.
  unfold problem_63_spec.
  unfold fibfib_fast.
  native_compute.
  reflexivity.
Qed.