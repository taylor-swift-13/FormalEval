Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.micromega.Lia.
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

(* Explicit proofs of fib_at for small fib numbers, constructed bottom-up *)

Lemma fib_0_0 : fib_at 0 0.
Proof. constructor. Qed.

Lemma fib_1_1 : fib_at 1 1.
Proof. constructor. Qed.

Lemma fib_2_1 : fib_at 2 1.
Proof.
  apply fib_at_S with (i:=0) (a:=0) (b:=1).
  - apply fib_0_0.
  - apply fib_1_1.
Qed.

Lemma fib_3_2 : fib_at 3 2.
Proof.
  apply fib_at_S with (i:=1) (a:=1) (b:=1).
  - apply fib_1_1.
  - apply fib_2_1.
Qed.

Lemma fib_4_3 : fib_at 4 3.
Proof.
  apply fib_at_S with (i:=2) (a:=1) (b:=2).
  - apply fib_2_1.
  - apply fib_3_2.
Qed.

Lemma fib_5_5 : fib_at 5 5.
Proof.
  apply fib_at_S with (i:=3) (a:=2) (b:=3).
  - apply fib_3_2.
  - apply fib_4_3.
Qed.

Lemma fib_6_8 : fib_at 6 8.
Proof.
  apply fib_at_S with (i:=4) (a:=3) (b:=5).
  - apply fib_4_3.
  - apply fib_5_5.
Qed.

Lemma fib_7_13 : fib_at 7 13.
Proof.
  apply fib_at_S with (i:=5) (a:=5) (b:=8).
  - apply fib_5_5.
  - apply fib_6_8.
Qed.

Lemma fib_8_21 : fib_at 8 21.
Proof.
  apply fib_at_S with (i:=6) (a:=8) (b:=13).
  - apply fib_6_8.
  - apply fib_7_13.
Qed.

Lemma fib_9_34 : fib_at 9 34.
Proof.
  apply fib_at_S with (i:=7) (a:=13) (b:=21).
  - apply fib_7_13.
  - apply fib_8_21.
Qed.

Lemma fib_10_55 : fib_at 10 55.
Proof.
  apply fib_at_S with (i:=8) (a:=21) (b:=34).
  - apply fib_8_21.
  - apply fib_9_34.
Qed.

Lemma fib_11_89 : fib_at 11 89.
Proof.
  apply fib_at_S with (i:=9) (a:=34) (b:=55).
  - apply fib_9_34.
  - apply fib_10_55.
Qed.

(* Primality proofs for required primes *)
Lemma prime_2 : IsPrime 2.
Proof.
  unfold IsPrime. split; [lia|].
  intros d Hdiv.
  destruct d; simpl in *; try lia.
  destruct d; simpl in *; try lia.
  right. reflexivity.
Qed.

Lemma prime_3 : IsPrime 3.
Proof.
  unfold IsPrime. split; [lia|].
  intros d Hdiv.
  destruct d; simpl in *; try lia.
  destruct d; simpl in *; try lia.
  destruct d; simpl in *; try lia.
  right. reflexivity.
Qed.

Lemma prime_5 : IsPrime 5.
Proof.
  unfold IsPrime. split; [lia|].
  intros d Hdiv.
  destruct d; simpl in *; try lia.
  destruct d; simpl in *; try lia.
  destruct d; simpl in *; try lia.
  destruct d; simpl in *; try lia.
  right. reflexivity.
Qed.

Lemma prime_13 : IsPrime 13.
Proof.
  unfold IsPrime. split; [lia|].
  intros d Hdiv.
  destruct d; simpl in *; try lia.
  destruct d; simpl in *; try lia.
  destruct d; simpl in *; try lia.
  destruct d; simpl in *; try lia.
  destruct d; simpl in *; try lia.
  right. reflexivity.
Qed.

Lemma prime_89 : IsPrime 89.
Proof.
  unfold IsPrime. split; [lia|].
  intros d Hdiv.
  destruct d; simpl in *; try lia.
  destruct d; simpl in *; try lia.
  destruct d; simpl in *; try lia.
  destruct d; simpl in *; try lia.
  destruct d; simpl in *; try lia.
  destruct d; simpl in *; try lia.
  right. reflexivity.
Qed.

(* Fib witnesses for primes *)

Lemma IsFib_2 : IsFib 2.
Proof. exists 3. apply fib_3_2. Qed.

Lemma IsFib_3 : IsFib 3.
Proof. exists 4. apply fib_4_3. Qed.

Lemma IsFib_5 : IsFib 5.
Proof. exists 5. apply fib_5_5. Qed.

Lemma IsFib_13 : IsFib 13.
Proof. exists 7. apply fib_7_13. Qed.

Lemma IsFib_89 : IsFib 89.
Proof. exists 11. apply fib_11_89. Qed.

(* Combine to IsPrimeFib *)

Lemma IsPrimeFib_2 : IsPrimeFib 2.
Proof. unfold IsPrimeFib. split; [apply prime_2 | apply IsFib_2]. Qed.

Lemma IsPrimeFib_3 : IsPrimeFib 3.
Proof. unfold IsPrimeFib. split; [apply prime_3 | apply IsFib_3]. Qed.

Lemma IsPrimeFib_5 : IsPrimeFib 5.
Proof. unfold IsPrimeFib. split; [apply prime_5 | apply IsFib_5]. Qed.

Lemma IsPrimeFib_13 : IsPrimeFib 13.
Proof. unfold IsPrimeFib. split; [apply prime_13 | apply IsFib_13]. Qed.

Lemma IsPrimeFib_89 : IsPrimeFib 89.
Proof. unfold IsPrimeFib. split; [apply prime_89 | apply IsFib_89]. Qed.

(* Test case: n = 1; output = 2 *)

Example prime_fib_1_spec : problem_39_spec 1 2.
Proof.
  unfold problem_39_spec.
  split.
  - apply IsPrimeFib_2.
  - exists [].
    repeat split.
    + simpl. reflexivity.
    + constructor.
    + intros y. split; intros H.
      * inversion H.
      * destruct H as [Hlt Hpf].
        (* For y < 2 and y prime fib, y must be less than 2 *)
        lia.
Qed.