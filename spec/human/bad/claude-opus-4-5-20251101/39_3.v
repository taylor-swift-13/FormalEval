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

Lemma five_is_prime : IsPrime 5.
Proof.
  unfold IsPrime. split.
  - lia.
  - intros d Hmod.
    destruct d as [|d']; [simpl in Hmod; discriminate|].
    destruct d' as [|d'']; [left; reflexivity|].
    destruct d'' as [|d''']; [simpl in Hmod; discriminate|].
    destruct d''' as [|d'''']; [simpl in Hmod; discriminate|].
    destruct d'''' as [|d''''']; [simpl in Hmod; discriminate|].
    destruct d''''' as [|d''''''].
    + right. reflexivity.
    + assert (Hge6: S (S (S (S (S (S d''''''))))) >= 6) by lia.
      assert (Hlt: 5 < S (S (S (S (S (S d'''''')))))) by lia.
      rewrite Nat.mod_small in Hmod by lia.
      discriminate.
Qed.

Lemma five_is_fib : IsFib 5.
Proof.
  unfold IsFib.
  exists 5.
  simpl. reflexivity.
Qed.

Lemma five_is_primefib : IsPrimeFib 5.
Proof.
  unfold IsPrimeFib.
  split.
  - exact five_is_prime.
  - exact five_is_fib.
Qed.

Lemma no_primefib_less_than_2 : forall y, y < 2 -> ~ IsPrimeFib y.
Proof.
  intros y Hy.
  unfold IsPrimeFib, IsPrime.
  intros [Hprime _].
  destruct Hprime as [H1 _].
  lia.
Qed.

Example test_problem_39_3 : problem_39_spec 3 5.
Proof.
  unfold problem_39_spec.
  split.
  - exact five_is_primefib.
  - exists [2; 3].
    split.
    + simpl. reflexivity.
    + split.
      * constructor.
        -- simpl. intros [H|[H|H]]; discriminate.
        -- constructor.
           ++ simpl. intros [H|H]; discriminate.
           ++ constructor.
      * intros y.
        split.
        -- intros H. simpl in H.
           destruct H as [H|[H|H]].
           ++ subst y. split. lia. exact two_is_primefib.
           ++ subst y. split. lia. exact three_is_primefib.
           ++ contradiction.
        -- intros [Hlt Hpf].
           destruct Hpf as [[Hgt1 Hdiv] Hfib].
           assert (y = 2 \/ y = 3) as Hy.
           {
             destruct y as [|y']; [lia|].
             destruct y' as [|y'']; [lia|].
             destruct y'' as [|y''']; [left; reflexivity|].
             destruct y''' as [|y'''']; [right; reflexivity|].
             lia.
           }
           destruct Hy as [Hy|Hy]; subst y.
           ++ simpl. left. reflexivity.
           ++ simpl. right. left. reflexivity.
Qed.