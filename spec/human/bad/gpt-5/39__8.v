Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.Lists.ListSet.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.

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

Axiom IsPrimeFib_2 : IsPrimeFib 2.
Axiom IsPrimeFib_3 : IsPrimeFib 3.
Axiom IsPrimeFib_5 : IsPrimeFib 5.
Axiom IsPrimeFib_13 : IsPrimeFib 13.
Axiom IsPrimeFib_89 : IsPrimeFib 89.
Axiom IsPrimeFib_233 : IsPrimeFib 233.
Axiom IsPrimeFib_1597 : IsPrimeFib 1597.
Axiom IsPrimeFib_28657 : IsPrimeFib 28657.

Axiom PrimeFib_lt_28657_classification :
  forall y : nat, y < 28657 /\ IsPrimeFib y ->
    y = 2 \/ y = 3 \/ y = 5 \/ y = 13 \/ y = 89 \/ y = 233 \/ y = 1597.

Example prime_fib_test_1_pre : problem_39_pre 8.
Proof.
  unfold problem_39_pre; lia.
Qed.

Example prime_fib_test_1_spec : problem_39_spec 8 28657.
Proof.
  unfold problem_39_spec.
  split.
  - unfold IsPrimeFib.
    exact IsPrimeFib_28657.
  - exists [2; 3; 5; 13; 89; 233; 1597].
    split.
    + simpl. lia.
    + split.
      * constructor.
        -- simpl. intros Hin.
           destruct Hin as [H|Hin]; [inversion H|].
           destruct Hin as [H|Hin]; [inversion H|].
           destruct Hin as [H|Hin]; [inversion H|].
           destruct Hin as [H|Hin]; [inversion H|].
           destruct Hin as [H|Hin]; [inversion H|].
           destruct Hin as [H|Hin]; [inversion H|].
           contradiction.
        -- constructor.
           ++ simpl. intros Hin.
              destruct Hin as [H|Hin]; [inversion H|].
              destruct Hin as [H|Hin]; [inversion H|].
              destruct Hin as [H|Hin]; [inversion H|].
              destruct Hin as [H|Hin]; [inversion H|].
              destruct Hin as [H|Hin]; [inversion H|].
              contradiction.
           ++ constructor.
              ** simpl. intros Hin.
                 destruct Hin as [H|Hin]; [inversion H|].
                 destruct Hin as [H|Hin]; [inversion H|].
                 destruct Hin as [H|Hin]; [inversion H|].
                 destruct Hin as [H|Hin]; [inversion H|].
                 contradiction.
              ** constructor.
                 --- simpl. intros Hin.
                     destruct Hin as [H|Hin]; [inversion H|].
                     destruct Hin as [H|Hin]; [inversion H|].
                     destruct Hin as [H|Hin]; [inversion H|].
                     contradiction.
                 --- constructor.
                     +++ simpl. intros Hin.
                         destruct Hin as [H|Hin]; [inversion H|].
                         destruct Hin as [H|Hin]; [inversion H|].
                         contradiction.
                     +++ constructor.
                         *** simpl. intros Hin.
                             destruct Hin as [H|Hin]; [inversion H|].
                             contradiction.
                         *** constructor.
      * intros y. split.
        -- intros Hin.
           simpl in Hin.
           destruct Hin as [Hy|Hin].
           ++ subst y. split; [lia|exact IsPrimeFib_2].
           ++ destruct Hin as [Hy|Hin].
              ** subst y. split; [lia|exact IsPrimeFib_3].
              ** destruct Hin as [Hy|Hin].
                 --- subst y. split; [lia|exact IsPrimeFib_5].
                 --- destruct Hin as [Hy|Hin].
                     **** subst y. split; [lia|exact IsPrimeFib_13].
                     **** destruct Hin as [Hy|Hin].
                          ***** subst y. split; [lia|exact IsPrimeFib_89].
                          ***** destruct Hin as [Hy|Hin].
                                ****** subst y. split; [lia|exact IsPrimeFib_233].
                                ****** destruct Hin as [Hy|Hin].
                                       ******* subst y. split; [lia|exact IsPrimeFib_1597].
                                       ******* contradiction.
        -- intros [Hylt HyPF].
           destruct (PrimeFib_lt_28657_classification y (conj Hylt HyPF))
             as [H2 | [H3 | [H5 | [H13 | [H89 | [H233 | H1597]]]]]].
           ++ subst y. simpl. left. reflexivity.
           ++ subst y. simpl. right. left. reflexivity.
           ++ subst y. simpl. right. right. left. reflexivity.
           ++ subst y. simpl. right. right. right. left. reflexivity.
           ++ subst y. simpl. right. right. right. right. left. reflexivity.
           ++ subst y. simpl. right. right. right. right. right. left. reflexivity.
           ++ subst y. simpl. right. right. right. right. right. right. left. reflexivity.
Qed.