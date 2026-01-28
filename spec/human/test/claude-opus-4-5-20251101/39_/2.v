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

Lemma IsPrime_2 : IsPrime 2.
Proof.
  unfold IsPrime. split.
  - lia.
  - intros d Hmod.
    destruct d as [|[|[|d']]].
    + simpl in Hmod. discriminate.
    + left. reflexivity.
    + right. reflexivity.
    + exfalso.
      assert (H: S (S (S d')) > 2) by lia.
      assert (H2: 2 mod S (S (S d')) = 2).
      { apply Nat.mod_small. lia. }
      rewrite H2 in Hmod. discriminate.
Qed.

Lemma IsPrime_3 : IsPrime 3.
Proof.
  unfold IsPrime. split.
  - lia.
  - intros d Hmod.
    destruct d as [|[|[|[|d']]]].
    + simpl in Hmod. discriminate.
    + left. reflexivity.
    + assert (H2: 3 mod 2 = 1) by reflexivity.
      rewrite H2 in Hmod. discriminate.
    + right. reflexivity.
    + exfalso.
      assert (H: S (S (S (S d'))) > 3) by lia.
      assert (H2: 3 mod S (S (S (S d'))) = 3).
      { apply Nat.mod_small. lia. }
      rewrite H2 in Hmod. discriminate.
Qed.

Lemma fib_at_3_2 : fib_at 3 2.
Proof.
  assert (H1: fib_at 2 1).
  { replace 1 with (0 + 1) by lia.
    apply fib_at_S.
    - apply fib_at_0.
    - apply fib_at_1. }
  replace 2 with (1 + 1) by lia.
  apply fib_at_S.
  - apply fib_at_1.
  - exact H1.
Qed.

Lemma fib_at_4_3 : fib_at 4 3.
Proof.
  assert (H1: fib_at 2 1).
  { replace 1 with (0 + 1) by lia.
    apply fib_at_S.
    - apply fib_at_0.
    - apply fib_at_1. }
  replace 3 with (1 + 2) by lia.
  apply fib_at_S.
  - exact H1.
  - apply fib_at_3_2.
Qed.

Lemma IsFib_2 : IsFib 2.
Proof.
  unfold IsFib. exists 3. apply fib_at_3_2.
Qed.

Lemma IsFib_3 : IsFib 3.
Proof.
  unfold IsFib. exists 4. apply fib_at_4_3.
Qed.

Lemma IsPrimeFib_2 : IsPrimeFib 2.
Proof.
  unfold IsPrimeFib. split.
  - apply IsPrime_2.
  - apply IsFib_2.
Qed.

Lemma IsPrimeFib_3 : IsPrimeFib 3.
Proof.
  unfold IsPrimeFib. split.
  - apply IsPrime_3.
  - apply IsFib_3.
Qed.

Lemma no_primefib_below_2 : forall y, y < 2 -> ~ IsPrimeFib y.
Proof.
  intros y Hy [Hprime _].
  unfold IsPrime in Hprime.
  destruct Hprime as [Hgt1 _].
  lia.
Qed.

Lemma only_primefib_2_below_3 : forall y, y < 3 -> IsPrimeFib y -> y = 2.
Proof.
  intros y Hy Hpf.
  destruct Hpf as [Hprime Hfib].
  unfold IsPrime in Hprime.
  destruct Hprime as [Hgt1 _].
  lia.
Qed.

Example problem_39_test1 : problem_39_spec 2 3.
Proof.
  unfold problem_39_spec.
  split.
  - apply IsPrimeFib_3.
  - exists [2].
    split.
    + simpl. reflexivity.
    + split.
      * constructor.
        -- simpl. tauto.
        -- constructor.
      * intros y. split.
        -- intros Hin. simpl in Hin.
           destruct Hin as [Heq | Hfalse].
           ++ subst y. split.
              ** lia.
              ** apply IsPrimeFib_2.
           ++ contradiction.
        -- intros [Hlt HprimeFib].
           assert (Hy2: y = 2) by (apply only_primefib_2_below_3; assumption).
           subst y. simpl. left. reflexivity.
Qed.