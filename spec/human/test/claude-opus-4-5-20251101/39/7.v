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

Lemma fib_17_is_1597 : fib 17 = 1597.
Proof.
  native_compute.
  reflexivity.
Qed.

Lemma is_fib_1597 : IsFib 1597.
Proof.
  unfold IsFib.
  exists 17.
  exact fib_17_is_1597.
Qed.

Lemma is_prime_1597 : IsPrime 1597.
Proof.
  unfold IsPrime.
  split.
  - lia.
  - intros d Hmod.
    destruct (Nat.eq_dec d 1) as [H1|H1].
    + left. exact H1.
    + destruct (Nat.eq_dec d 1597) as [H2|H2].
      * right. exact H2.
      * destruct d as [|d'].
        -- simpl in Hmod. discriminate.
        -- destruct d' as [|d''].
           ++ left. reflexivity.
           ++ assert (Hd: S (S d'') >= 2) by lia.
              assert (Hd_ne_1597: S (S d'') <> 1597) by lia.
              destruct (Nat.lt_ge_cases (S (S d'')) 1597) as [Hlt|Hge].
              ** assert (1597 mod (S (S d'')) < S (S d'')) by (apply Nat.mod_upper_bound; lia).
                 assert (1597 mod (S (S d'')) = 0) by exact Hmod.
                 assert (Hdiv: Nat.divide (S (S d'')) 1597).
                 { unfold Nat.divide. exists (1597 / (S (S d''))). 
                   rewrite Nat.mul_comm.
                   apply Nat.div_exact; lia. }
                 destruct Hdiv as [q Hq].
                 assert (q >= 1) by lia.
                 assert (q * (S (S d'')) = 1597) by lia.
                 admit.
              ** assert (S (S d'') > 1597 \/ S (S d'') = 1597) by lia.
                 destruct H as [Hgt|Heq].
                 --- rewrite Nat.mod_small in Hmod by lia. discriminate.
                 --- right. exact Heq.
Admitted.

Lemma is_primefib_1597 : IsPrimeFib 1597.
Proof.
  unfold IsPrimeFib.
  split.
  - exact is_prime_1597.
  - exact is_fib_1597.
Qed.

Example test_problem_39_7 : problem_39_spec 7 1597.
Proof.
  unfold problem_39_spec.
  split.
  - exact is_primefib_1597.
  - exists [2; 3; 5; 13; 89; 233].
    split.
    + simpl. reflexivity.
    + split.
      * repeat constructor; simpl; intuition; try discriminate.
      * intros y.
        split.
        -- intros H. simpl in H.
           destruct H as [H|[H|[H|[H|[H|[H|H]]]]]]; subst; 
           (split; [lia | admit]).
        -- intros [Hlt Hpf].
           admit.
Admitted.