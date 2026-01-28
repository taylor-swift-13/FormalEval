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

Fixpoint fibfib_iter (n : nat) (a b c : Z) : Z :=
  match n with
  | 0%nat => a
  | S n' => fibfib_iter n' b c (a + b + c)
  end.

Definition fibfib_fast (n : nat) : Z :=
  fibfib_iter n 0 0 1.

Lemma fibfib_iter_correct : forall k n a b c,
  a = fibfib_Z n ->
  b = fibfib_Z (S n) ->
  c = fibfib_Z (S (S n)) ->
  fibfib_iter k a b c = fibfib_Z (k + n).
Proof.
  induction k; intros n a b c Ha Hb Hc.
  - simpl. rewrite Nat.add_0_l. exact Ha.
  - simpl. rewrite IHk with (n := S n).
    + f_equal. lia.
    + exact Hb.
    + exact Hc.
    + subst. destruct n as [|[|[|n']]]; simpl; ring.
Qed.

Lemma fibfib_fast_correct : forall n, fibfib_fast n = fibfib_Z n.
Proof.
  intros n.
  unfold fibfib_fast.
  rewrite fibfib_iter_correct with (n := 0%nat).
  - rewrite Nat.add_0_r. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Example test_fibfib_58 : problem_63_spec 58 408933139743937.
Proof.
  unfold problem_63_spec.
  rewrite <- fibfib_fast_correct.
  native_compute.
  reflexivity.
Qed.