Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import ZArith.
Import ListNotations.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, d <> 0 -> n mod d = 0 -> d = 1 \/ d = n).

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
            | 0 => 1
            | S n'' => fib n' + fib n''
            end
  end.

Definition IsFib (n : nat) : Prop := exists i : nat, fib i = n.

Definition IsPrimeFib (n : nat) : Prop :=
  IsPrime n /\ IsFib n.

Definition problem_39_spec (n r : nat) : Prop :=
  IsPrimeFib r /\
  (exists (S : list nat),
    length S = n - 1 /\
    NoDup S /\
    (forall y : nat, In y S <-> (y < r /\ IsPrimeFib y))
  ).

Example test_case : problem_39_spec 1 2.
Proof.
  unfold problem_39_spec.
  split.
  - unfold IsPrimeFib.
    split.
    + unfold IsPrime.
      split.
      * apply Nat.lt_1_2.
      * intros d Hd0 Hmod.
        destruct d.
        { contradiction. }
        destruct d.
        { left. reflexivity. }
        right.
        assert (H : 2 < S (S d)).
        { apply Nat.lt_succ_diag_r. }
        apply le_n_S.
        apply le_n_S.
        apply Nat.le_0_l.
    + unfold IsFib.
      exists 3.
      simpl.
      reflexivity.
  - exists [].
    repeat split.
    + simpl. rewrite Nat.sub_1_r. reflexivity.
    + apply NoDup_nil.
    + intros y.
      split.
      * intros H.
        inversion H.
      * intros [Hlt Hpf].
        exfalso.
        apply (Nat.nlt_0_r y).
        assumption.
Qed.