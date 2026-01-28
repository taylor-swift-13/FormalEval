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
    + exfalso. simpl in Hmod. discriminate.
    + right. reflexivity.
    + exfalso.
      assert (H2: 3 mod S (S (S (S d'))) = 3).
      { apply Nat.mod_small. lia. }
      rewrite H2 in Hmod. discriminate.
Qed.

Lemma IsPrime_5 : IsPrime 5.
Proof.
  unfold IsPrime. split.
  - lia.
  - intros d Hmod.
    destruct d as [|[|[|[|[|[|d']]]]]].
    + simpl in Hmod. discriminate.
    + left. reflexivity.
    + exfalso. simpl in Hmod. discriminate.
    + exfalso. simpl in Hmod. discriminate.
    + exfalso. simpl in Hmod. discriminate.
    + right. reflexivity.
    + exfalso.
      assert (H2: 5 mod S (S (S (S (S (S d'))))) = 5).
      { apply Nat.mod_small. lia. }
      rewrite H2 in Hmod. discriminate.
Qed.

Lemma fib_at_2_1 : fib_at 2 1.
Proof.
  replace 1 with (0 + 1) by lia.
  apply fib_at_S.
  - apply fib_at_0.
  - apply fib_at_1.
Qed.

Lemma fib_at_3_2 : fib_at 3 2.
Proof.
  replace 2 with (1 + 1) by lia.
  apply fib_at_S.
  - apply fib_at_1.
  - apply fib_at_2_1.
Qed.

Lemma fib_at_4_3 : fib_at 4 3.
Proof.
  replace 3 with (1 + 2) by lia.
  apply fib_at_S.
  - apply fib_at_2_1.
  - apply fib_at_3_2.
Qed.

Lemma fib_at_5_5 : fib_at 5 5.
Proof.
  replace 5 with (2 + 3) by lia.
  apply fib_at_S.
  - apply fib_at_3_2.
  - apply fib_at_4_3.
Qed.

Lemma IsFib_2 : IsFib 2.
Proof.
  unfold IsFib. exists 3. apply fib_at_3_2.
Qed.

Lemma IsFib_3 : IsFib 3.
Proof.
  unfold IsFib. exists 4. apply fib_at_4_3.
Qed.

Lemma IsFib_5 : IsFib 5.
Proof.
  unfold IsFib. exists 5. apply fib_at_5_5.
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

Lemma IsPrimeFib_5 : IsPrimeFib 5.
Proof.
  unfold IsPrimeFib. split.
  - apply IsPrime_5.
  - apply IsFib_5.
Qed.

Lemma no_primefib_below_2 : forall y, y < 2 -> ~ IsPrimeFib y.
Proof.
  intros y Hy [Hprime _].
  unfold IsPrime in Hprime.
  destruct Hprime as [Hgt1 _].
  lia.
Qed.

Lemma not_IsPrime_4 : ~ IsPrime 4.
Proof.
  unfold IsPrime. intros [_ Hdiv].
  specialize (Hdiv 2).
  assert (H: 4 mod 2 = 0) by reflexivity.
  specialize (Hdiv H).
  destruct Hdiv; discriminate.
Qed.

Lemma primefib_below_5 : forall y, y < 5 -> IsPrimeFib y -> y = 2 \/ y = 3.
Proof.
  intros y Hy Hpf.
  destruct Hpf as [Hprime Hfib].
  unfold IsPrime in Hprime.
  destruct Hprime as [Hgt1 _].
  destruct y as [|[|[|[|[|y']]]]]; try lia.
  - right. reflexivity.
  - left. reflexivity.
Qed.

Example problem_39_test1 : problem_39_spec 3 5.
Proof.
  unfold problem_39_spec.
  split.
  - apply IsPrimeFib_5.
  - exists [2; 3].
    split.
    + simpl. reflexivity.
    + split.
      * constructor.
        -- simpl. intros [H|[H|H]]; discriminate.
        -- constructor.
           ++ simpl. intros [].
           ++ constructor.
      * intros y. split.
        -- intros Hin.
           simpl in Hin.
           destruct Hin as [H|[H|H]].
           ++ subst. split. lia. apply IsPrimeFib_2.
           ++ subst. split. lia. apply IsPrimeFib_3.
           ++ contradiction.
        -- intros [Hlt HprimeFib].
           simpl.
           destruct (primefib_below_5 y Hlt HprimeFib) as [Hy|Hy]; subst.
           ++ left. reflexivity.
           ++ right. left. reflexivity.
Qed.