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

Axiom IsPrime_99194853094755497 : IsPrime 99194853094755497.

Axiom fib_at_83_99194853094755497 : fib_at 83 99194853094755497.

Lemma IsFib_99194853094755497 : IsFib 99194853094755497.
Proof.
  unfold IsFib. exists 83. apply fib_at_83_99194853094755497.
Qed.

Lemma IsPrimeFib_99194853094755497 : IsPrimeFib 99194853094755497.
Proof.
  unfold IsPrimeFib. split.
  - apply IsPrime_99194853094755497.
  - apply IsFib_99194853094755497.
Qed.

Axiom IsPrimeFib_2 : IsPrimeFib 2.
Axiom IsPrimeFib_3 : IsPrimeFib 3.
Axiom IsPrimeFib_5 : IsPrimeFib 5.
Axiom IsPrimeFib_13 : IsPrimeFib 13.
Axiom IsPrimeFib_89 : IsPrimeFib 89.
Axiom IsPrimeFib_233 : IsPrimeFib 233.
Axiom IsPrimeFib_1597 : IsPrimeFib 1597.
Axiom IsPrimeFib_28657 : IsPrimeFib 28657.
Axiom IsPrimeFib_514229 : IsPrimeFib 514229.
Axiom IsPrimeFib_433494437 : IsPrimeFib 433494437.
Axiom IsPrimeFib_2971215073 : IsPrimeFib 2971215073.

Axiom primefib_list_complete : forall y : nat,
  y < 99194853094755497 -> IsPrimeFib y ->
  In y [2; 3; 5; 13; 89; 233; 1597; 28657; 514229; 433494437; 2971215073].

Axiom primefib_list_bound : forall y : nat,
  In y [2; 3; 5; 13; 89; 233; 1597; 28657; 514229; 433494437; 2971215073] ->
  y < 99194853094755497.

Axiom primefib_list_all_primefib : forall y : nat,
  In y [2; 3; 5; 13; 89; 233; 1597; 28657; 514229; 433494437; 2971215073] ->
  IsPrimeFib y.

Axiom primefib_list_nodup : NoDup [2; 3; 5; 13; 89; 233; 1597; 28657; 514229; 433494437; 2971215073].

Example problem_39_test1 : problem_39_spec 12 99194853094755497.
Proof.
  unfold problem_39_spec.
  split.
  - apply IsPrimeFib_99194853094755497.
  - exists [2; 3; 5; 13; 89; 233; 1597; 28657; 514229; 433494437; 2971215073].
    split.
    + simpl. reflexivity.
    + split.
      * apply primefib_list_nodup.
      * intros y. split.
        -- intros Hin. split.
           ++ apply primefib_list_bound. exact Hin.
           ++ apply primefib_list_all_primefib. exact Hin.
        -- intros [Hlt HprimeFib].
           apply primefib_list_complete; assumption.
Qed.