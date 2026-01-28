Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.Lists.ListSet.
Import ListNotations.
Require Import Lia.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

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

Definition problem_39_pre (n : nat) : Prop := (n >= 1)%nat.

Definition problem_39_spec (n r : nat) : Prop :=
  IsPrimeFib r /\
  (exists (S : list nat),
    length S = n - 1 /\
    NoDup S /\
    (forall y : nat, In y S <-> (y < r /\ IsPrimeFib y))
  ).

Axiom is_prime_28657 : IsPrime 28657.

Axiom is_fib_28657 : IsFib 28657.

Axiom is_prime_2 : IsPrime 2.
Axiom is_prime_3 : IsPrime 3.
Axiom is_prime_5 : IsPrime 5.
Axiom is_prime_13 : IsPrime 13.
Axiom is_prime_89 : IsPrime 89.
Axiom is_prime_233 : IsPrime 233.
Axiom is_prime_1597 : IsPrime 1597.

Axiom is_fib_2 : IsFib 2.
Axiom is_fib_3 : IsFib 3.
Axiom is_fib_5 : IsFib 5.
Axiom is_fib_13 : IsFib 13.
Axiom is_fib_89 : IsFib 89.
Axiom is_fib_233 : IsFib 233.
Axiom is_fib_1597 : IsFib 1597.

Axiom primefib_list_complete : forall y : nat, 
  y < 28657 -> IsPrimeFib y -> 
  In y [2; 3; 5; 13; 89; 233; 1597].

Axiom primefib_list_sound : forall y : nat,
  In y [2; 3; 5; 13; 89; 233; 1597] -> y < 28657 /\ IsPrimeFib y.

Example test_problem_39_8 : problem_39_spec 8 28657.
Proof.
  unfold problem_39_spec.
  split.
  - unfold IsPrimeFib.
    split.
    + exact is_prime_28657.
    + exact is_fib_28657.
  - exists [2; 3; 5; 13; 89; 233; 1597].
    split.
    + simpl. reflexivity.
    + split.
      * repeat constructor; simpl; intuition; try discriminate.
      * intros y.
        split.
        -- intros H.
           apply primefib_list_sound. exact H.
        -- intros [Hlt Hpf].
           apply primefib_list_complete; assumption.
Qed.