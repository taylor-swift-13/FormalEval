Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.

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

Definition problem_63_pre (n : nat) : Prop := True.

Definition problem_63_spec (n : nat) (res : nat) : Prop :=
  res = fibfib n.

Fixpoint fibfib_linear (n : nat) (a b c : nat) : nat :=
  match n with
  | 0 => a
  | S n' => fibfib_linear n' b c (a + b + c)
  end.

Lemma fibfib_linear_spec : forall n k,
  fibfib_linear n (fibfib k) (fibfib (S k)) (fibfib (S (S k))) = fibfib (n + k).
Proof.
  induction n as [| n IH]; intros k.
  - simpl. rewrite Nat.add_0_l. reflexivity.
  - simpl. rewrite <- (IH (S k)).
    f_equal. f_equal. f_equal.
    simpl. ring.
Qed.

Example test_problem_63 : problem_63_spec 30 15902591.
Proof.
  unfold problem_63_spec.
  rewrite <- (Nat.add_0_r 30).
  rewrite <- (fibfib_linear_spec 30 0).
  vm_compute.
  reflexivity.
Qed.