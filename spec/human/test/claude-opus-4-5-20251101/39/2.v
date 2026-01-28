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

Lemma two_is_prime : IsPrime 2.
Proof.
  unfold IsPrime. split.
  - lia.
  - intros d Hmod.
    destruct d as [|d'].
    + simpl in Hmod. discriminate.
    + destruct d' as [|d''].
      * left. reflexivity.
      * destruct d'' as [|d'''].
        -- right. reflexivity.
        -- assert (Hge3: S (S (S d''')) >= 3) by lia.
           assert (Hlt: 2 < S (S (S d'''))) by lia.
           rewrite Nat.mod_small in Hmod by lia.
           discriminate.
Qed.

Lemma two_is_fib : IsFib 2.
Proof.
  unfold IsFib.
  exists 3.
  simpl. reflexivity.
Qed.

Lemma two_is_primefib : IsPrimeFib 2.
Proof.
  unfold IsPrimeFib.
  split.
  - exact two_is_prime.
  - exact two_is_fib.
Qed.

Lemma three_is_prime : IsPrime 3.
Proof.
  unfold IsPrime. split.
  - lia.
  - intros d Hmod.
    destruct d as [|d'].
    + simpl in Hmod. discriminate.
    + destruct d' as [|d''].
      * left. reflexivity.
      * destruct d'' as [|d'''].
        -- simpl in Hmod. discriminate.
        -- destruct d''' as [|d''''].
           ++ right. reflexivity.
           ++ assert (Hge4: S (S (S (S d''''))) >= 4) by lia.
              assert (Hlt: 3 < S (S (S (S d'''')))) by lia.
              rewrite Nat.mod_small in Hmod by lia.
              discriminate.
Qed.

Lemma three_is_fib : IsFib 3.
Proof.
  unfold IsFib.
  exists 4.
  simpl. reflexivity.
Qed.

Lemma three_is_primefib : IsPrimeFib 3.
Proof.
  unfold IsPrimeFib.
  split.
  - exact three_is_prime.
  - exact three_is_fib.
Qed.

Lemma no_primefib_less_than_2 : forall y, y < 2 -> ~ IsPrimeFib y.
Proof.
  intros y Hy.
  unfold IsPrimeFib, IsPrime.
  intros [Hprime _].
  destruct Hprime as [H1 _].
  lia.
Qed.

Lemma only_primefib_2_less_than_3 : forall y, y < 3 -> IsPrimeFib y -> y = 2.
Proof.
  intros y Hy Hpf.
  unfold IsPrimeFib, IsPrime in Hpf.
  destruct Hpf as [[H1 _] _].
  lia.
Qed.

Example test_problem_39_2 : problem_39_spec 2 3.
Proof.
  unfold problem_39_spec.
  split.
  - exact three_is_primefib.
  - exists [2].
    split.
    + simpl. reflexivity.
    + split.
      * constructor.
        -- simpl. tauto.
        -- constructor.
      * intros y.
        split.
        -- intros H. simpl in H.
           destruct H as [H | H].
           ++ subst y. split. lia. exact two_is_primefib.
           ++ contradiction.
        -- intros [Hlt Hpf].
           assert (Heq: y = 2) by (apply only_primefib_2_less_than_3; assumption).
           subst y. simpl. left. reflexivity.
Qed.