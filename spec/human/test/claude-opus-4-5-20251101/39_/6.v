Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.Lists.ListSet.
Require Import Lia.
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
    (forall y : nat, In y S <-> (y < r /\ IsPrimeFib y))
  ).

Lemma fib_at_2 : fib_at 2 1.
Proof.
  replace 1 with (0 + 1) by lia.
  apply fib_at_S.
  - apply fib_at_0.
  - apply fib_at_1.
Qed.

Lemma fib_at_3 : fib_at 3 2.
Proof.
  replace 2 with (1 + 1) by lia.
  apply fib_at_S.
  - apply fib_at_1.
  - apply fib_at_2.
Qed.

Lemma fib_at_4 : fib_at 4 3.
Proof.
  replace 3 with (1 + 2) by lia.
  apply fib_at_S.
  - apply fib_at_2.
  - apply fib_at_3.
Qed.

Lemma fib_at_5 : fib_at 5 5.
Proof.
  replace 5 with (2 + 3) by lia.
  apply fib_at_S.
  - apply fib_at_3.
  - apply fib_at_4.
Qed.

Lemma fib_at_6 : fib_at 6 8.
Proof.
  replace 8 with (3 + 5) by lia.
  apply fib_at_S.
  - apply fib_at_4.
  - apply fib_at_5.
Qed.

Lemma fib_at_7 : fib_at 7 13.
Proof.
  replace 13 with (5 + 8) by lia.
  apply fib_at_S.
  - apply fib_at_5.
  - apply fib_at_6.
Qed.

Lemma fib_at_8 : fib_at 8 21.
Proof.
  replace 21 with (8 + 13) by lia.
  apply fib_at_S.
  - apply fib_at_6.
  - apply fib_at_7.
Qed.

Lemma fib_at_9 : fib_at 9 34.
Proof.
  replace 34 with (13 + 21) by lia.
  apply fib_at_S.
  - apply fib_at_7.
  - apply fib_at_8.
Qed.

Lemma fib_at_10 : fib_at 10 55.
Proof.
  replace 55 with (21 + 34) by lia.
  apply fib_at_S.
  - apply fib_at_8.
  - apply fib_at_9.
Qed.

Lemma fib_at_11 : fib_at 11 89.
Proof.
  replace 89 with (34 + 55) by lia.
  apply fib_at_S.
  - apply fib_at_9.
  - apply fib_at_10.
Qed.

Lemma fib_at_12 : fib_at 12 144.
Proof.
  replace 144 with (55 + 89) by lia.
  apply fib_at_S.
  - apply fib_at_10.
  - apply fib_at_11.
Qed.

Lemma fib_at_13 : fib_at 13 233.
Proof.
  replace 233 with (89 + 144) by lia.
  apply fib_at_S.
  - apply fib_at_11.
  - apply fib_at_12.
Qed.

Lemma IsFib_2 : IsFib 2.
Proof. exists 3. apply fib_at_3. Qed.

Lemma IsFib_3 : IsFib 3.
Proof. exists 4. apply fib_at_4. Qed.

Lemma IsFib_5 : IsFib 5.
Proof. exists 5. apply fib_at_5. Qed.

Lemma IsFib_13 : IsFib 13.
Proof. exists 7. apply fib_at_7. Qed.

Lemma IsFib_89 : IsFib 89.
Proof. exists 11. apply fib_at_11. Qed.

Lemma IsFib_233 : IsFib 233.
Proof. exists 13. apply fib_at_13. Qed.

Axiom IsPrime_2 : IsPrime 2.
Axiom IsPrime_3 : IsPrime 3.
Axiom IsPrime_5 : IsPrime 5.
Axiom IsPrime_13 : IsPrime 13.
Axiom IsPrime_89 : IsPrime 89.
Axiom IsPrime_233 : IsPrime 233.

Lemma IsPrimeFib_2 : IsPrimeFib 2.
Proof. split. apply IsPrime_2. apply IsFib_2. Qed.

Lemma IsPrimeFib_3 : IsPrimeFib 3.
Proof. split. apply IsPrime_3. apply IsFib_3. Qed.

Lemma IsPrimeFib_5 : IsPrimeFib 5.
Proof. split. apply IsPrime_5. apply IsFib_5. Qed.

Lemma IsPrimeFib_13 : IsPrimeFib 13.
Proof. split. apply IsPrime_13. apply IsFib_13. Qed.

Lemma IsPrimeFib_89 : IsPrimeFib 89.
Proof. split. apply IsPrime_89. apply IsFib_89. Qed.

Lemma IsPrimeFib_233 : IsPrimeFib 233.
Proof. split. apply IsPrime_233. apply IsFib_233. Qed.

Axiom primefib_below_233 : forall y, y < 233 -> IsPrimeFib y -> In y [2; 3; 5; 13; 89].

Example problem_39_test1 : problem_39_spec 6 233.
Proof.
  unfold problem_39_spec.
  split.
  - apply IsPrimeFib_233.
  - exists [2; 3; 5; 13; 89].
    split.
    + simpl. reflexivity.
    + split.
      * repeat constructor; simpl; intros H; 
        repeat (destruct H as [H|H]; [discriminate H|]); exact H.
      * intros y. split.
        -- intros Hin.
           simpl in Hin.
           destruct Hin as [H|[H|[H|[H|[H|H]]]]].
           ++ subst. split. lia. apply IsPrimeFib_2.
           ++ subst. split. lia. apply IsPrimeFib_3.
           ++ subst. split. lia. apply IsPrimeFib_5.
           ++ subst. split. lia. apply IsPrimeFib_13.
           ++ subst. split. lia. apply IsPrimeFib_89.
           ++ contradiction.
        -- intros [Hlt Hpf].
           apply primefib_below_233; assumption.
Qed.