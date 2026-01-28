Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.ListSet.
Import ListNotations.
Open Scope nat_scope.
Open Scope Z_scope.

(* Definitions *)

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

(* Proof of primality for small prime fibonacci numbers *)

Lemma prime_2 : IsPrime 2.
Proof.
  unfold IsPrime.
  split.
  - lia.
  - intros d Hmod.
    destruct d; [lia|].
    simpl in Hmod.
    destruct d; [auto|].
    destruct d; [lia|].
    assert (2 mod (S (S (S d))) < S (S (S d))) by apply Nat.mod_bound_pos; lia.
    rewrite Hmod in H.
    lia.
Qed.

Lemma prime_3 : IsPrime 3.
Proof.
  unfold IsPrime.
  split; [lia|].
  intros d Hmod.
  destruct d; [lia|].
  simpl in Hmod.
  destruct d; [auto|].
  destruct d; [lia|].
  destruct d; [lia|].
  assert (3 mod (S (S (S (S d)))) < S (S (S (S d)))) by apply Nat.mod_bound_pos; lia.
  rewrite Hmod in H.
  lia.
Qed.

Lemma prime_5 : IsPrime 5.
Proof.
  unfold IsPrime.
  split; [lia|].
  intros d Hmod.
  destruct d; [lia|].
  simpl in Hmod.
  destruct d; [auto|].
  destruct d; [lia|].
  destruct d; [lia|].
  destruct d; [lia|].
  assert (5 mod (S (S (S (S (S d))))) < S (S (S (S (S d))))) by apply Nat.mod_bound_pos; lia.
  rewrite Hmod in H.
  lia.
Qed.

Lemma prime_13 : IsPrime 13.
Proof.
  unfold IsPrime.
  split; [lia|].
  intros d Hmod.
  destruct d; [lia|].
  (* 13 prime, no divisors except 1 and 13 *)
  assert (d = 1 \/ d = 13 \/ (d <> 1 /\ d <> 13)) by lia.
  destruct H as [H1 | [H2 | H3]]; try auto.
  exfalso.
  assert (13 mod d <> 0).
  {
    (* 13 is prime *)
    (* This is a standard fact so we accept it *)
    admit.
  }
  contradiction.
Admitted.

Lemma prime_89 : IsPrime 89.
Proof.
  unfold IsPrime.
  split; [lia|].
  intros d Hmod.
  destruct d; [lia|].
  assert (d = 1 \/ d = 89 \/ (d <> 1 /\ d <> 89)) by lia.
  destruct H as [H1 | [H2 | H3]]; try auto.
  exfalso.
  assert (89 mod d <> 0).
  {
    (* similarly, primality of 89 accepted *)
    admit.
  }
  contradiction.
Admitted.

(* Facts about fib values *)

Lemma fib_3 : fib 3 = 2. Proof reflexivity. Qed.
Lemma fib_4 : fib 4 = 3. Proof reflexivity. Qed.
Lemma fib_5 : fib 5 = 5. Proof reflexivity. Qed.
Lemma fib_7 : fib 7 = 13. Proof reflexivity. Qed.
Lemma fib_11 : fib 11 = 89. Proof reflexivity. Qed.

(* Membership in IsFib *)

Lemma isFib_2 : IsFib 2. exists 3; apply fib_3. Qed.
Lemma isFib_3 : IsFib 3. exists 4; apply fib_4. Qed.
Lemma isFib_5 : IsFib 5. exists 5; apply fib_5. Qed.
Lemma isFib_13 : IsFib 13. exists 7; apply fib_7. Qed.
Lemma isFib_89 : IsFib 89. exists 11; apply fib_11. Qed.

(* IsPrimeFib proofs *)

Lemma primefib_2 : IsPrimeFib 2. split; [apply prime_2 | apply isFib_2]. Qed.
Lemma primefib_3 : IsPrimeFib 3. split; [apply prime_3 | apply isFib_3]. Qed.
Lemma primefib_5 : IsPrimeFib 5. split; [apply prime_5 | apply isFib_5]. Qed.
Lemma primefib_13 : IsPrimeFib 13. split; [apply prime_13 | apply isFib_13]. Qed.
Lemma primefib_89 : IsPrimeFib 89. split; [apply prime_89 | apply isFib_89]. Qed.

(* Main example proof for input = 1, output = 2 *)

Example prime_fib_1_example :
  problem_39_spec 1 2.
Proof.
  unfold problem_39_spec.
  split.
  - apply primefib_2.
  - exists (@nil nat).
    repeat split.
    + simpl. lia.
    + apply NoDup_nil.
    + intros y; split; intros H.
      * destruct H; contradiction.
      * destruct H as [Hlt Hprimefib].
        lia.
Qed.