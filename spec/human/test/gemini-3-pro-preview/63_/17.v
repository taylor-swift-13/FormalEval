Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.

Inductive is_fibfib : nat -> nat -> Prop :=
  | ff_zero : is_fibfib 0 0
  | ff_one  : is_fibfib 1 0
  | ff_two  : is_fibfib 2 1
  | ff_step : forall n res_n res_n1 res_n2,
      is_fibfib n res_n ->
      is_fibfib (S n) res_n1 ->
      is_fibfib (S (S n)) res_n2 ->
      is_fibfib (S (S (S n))) (res_n + res_n1 + res_n2).

Definition problem_63_pre (n : nat) : Prop := True.

Definition problem_63_spec (n : nat) (res : nat) : Prop :=
  is_fibfib n res.

Fixpoint fibfib_fun (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n1 =>
    match n1 with
    | 0 => 0
    | S n2 =>
      match n2 with
      | 0 => 1
      | S n3 => fibfib_fun n3 + fibfib_fun n2 + fibfib_fun n1
      end
    end
  end.

Lemma fibfib_correct_strong : forall n, 
  is_fibfib n (fibfib_fun n) /\ 
  is_fibfib (S n) (fibfib_fun (S n)) /\ 
  is_fibfib (S (S n)) (fibfib_fun (S (S n))).
Proof.
  intro n. induction n.
  - repeat split; constructor.
  - destruct IHn as [H1 [H2 H3]].
    repeat split.
    + exact H2.
    + exact H3.
    + simpl. apply ff_step.
      * exact H1.
      * exact H2.
      * exact H3.
Qed.

Lemma fibfib_correct : forall n, is_fibfib n (fibfib_fun n).
Proof.
  intro n. destruct (fibfib_correct_strong n) as [H _]. apply H.
Qed.

Example test_fibfib_22 : problem_63_spec 22 121415.
Proof.
  unfold problem_63_spec.
  replace 121415 with (fibfib_fun 22) by reflexivity.
  apply fibfib_correct.
Qed.