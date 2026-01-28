Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.Lists.ListSet.
Import ListNotations.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Inductive fib_at : nat -> nat -> Prop :=
| fib_at_0 : fib_at 0 0
| fib_at_1 : fib_at 1 1
| fib_at_S : forall i a b,
    fib_at i a ->
    fib_at (S i) b ->
    fib_at (S (S i)) (a + b).

Definition IsFib (n : nat) : Prop := exists i : nat, fib_at i n.

Definition IsPrimeFib (n : nat) : Prop :=
  IsPrime n /\ IsFib n.

Definition problem_39_pre (n : nat) : Prop := (n >= 1)%nat.

Definition problem_39_spec (n r : nat) : Prop :=
  IsPrimeFib r /\
  (exists (S : list nat),
    length S = n - 1 /\
    NoDup S /\
    (forall y : nat, In y S <-> (y < r /\ IsPrimeFib y))).

Lemma prime_2 : IsPrime 2.
Proof.
  unfold IsPrime.
  split.
  - unfold lt. apply le_n_S. apply le_n_S. apply le_0_n.
  - intros d H.
    destruct d as [| [| [| d']]].
    + inversion H.
    + left. reflexivity.
    + right. reflexivity.
    + inversion H.
Qed.

Lemma fib_at_2 : fib_at 3 2.
Proof.
  apply (fib_at_S 1 1 1).
  - apply fib_at_1.
  - apply (fib_at_S 0 0 1).
    + apply fib_at_0.
    + apply fib_at_1.
Qed.

Lemma fib_2 : IsFib 2.
Proof.
  unfold IsFib.
  exists 3.
  apply fib_at_2.
Qed.

Lemma prime_fib_2 : IsPrimeFib 2.
Proof.
  unfold IsPrimeFib.
  split.
  - apply prime_2.
  - apply fib_2.
Qed.

Lemma no_prime_fib_below_2 : forall y, y < 2 -> ~IsPrimeFib y.
Proof.
  intros y H.
  unfold not.
  intros H1.
  unfold IsPrimeFib in H1.
  destruct H1 as [Hprime _].
  unfold IsPrime in Hprime.
  destruct Hprime as [Hlt _].
  destruct y.
  - inversion Hlt.
  - destruct y.
    + inversion Hlt.
    + simpl in H. inversion H.
Qed.

Example prime_fib_1 : problem_39_spec 1 2.
Proof.
  unfold problem_39_spec.
  split.
  - apply prime_fib_2.
  - exists [].
    repeat split.
    + simpl. reflexivity.
    + apply NoDup_nil.
    + intros y.
      split.
      * intros H. inversion H.
      * intros [Hlt Hpf].
        assert (Hcontra := no_prime_fib_below_2 y Hlt).
        contradiction.
Qed.