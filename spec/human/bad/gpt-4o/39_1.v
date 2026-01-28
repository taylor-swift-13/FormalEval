Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.Lists.ListSet.
Import ListNotations.

Require Import Coq.micromega.Lia.

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

Definition IsFib (n : nat) : Prop :=
  exists i : nat, fib i = n.

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

Open Scope nat_scope.

(* Helper Lemmas *)

Lemma fib_2 : fib 3 = 2.
Proof.
  simpl. reflexivity.
Qed.

Lemma fib_3 : fib 4 = 3.
Proof.
  simpl. reflexivity.
Qed.

Lemma fib_5 : fib 5 = 5.
Proof.
  simpl. reflexivity.
Qed.

Lemma prime_2 : IsPrime 2.
Proof.
  split.
  - simpl. lia.
  - intros d H. destruct d; simpl in H. 
    + destruct (Nat.mod_divides 2 0) as [k Hk]; try lia.
    + destruct d.
      * simpl in H. left. reflexivity.
      * destruct d; simpl in *.
        -- right. reflexivity.
        -- exfalso. apply Nat.divides_le in H. lia. 
Qed.

Lemma prime_3 : IsPrime 3.
Proof.
  split.
  - simpl. lia.
  - intros d H. destruct d; simpl in H.
    + destruct (Nat.mod_divides 3 0) as [k Hk]; try lia.
    + destruct d.
      * simpl in H. left. reflexivity.
      * destruct d. 
        -- right. reflexivity.
        -- exfalso. apply Nat.divides_le in H. lia. 
Qed.

Lemma prime_5 : IsPrime 5.
Proof.
  split.
  - simpl. lia.
  - intros d H. destruct d; simpl in H.
    + destruct (Nat.mod_divides 5 0) as [k Hk]; try lia.
    + destruct d.
      * simpl in H. left. reflexivity.
      * destruct d; simpl in *.
        -- destruct d.
           ++ right. reflexivity.
           ++ exfalso. apply Nat.divides_le in H. lia.
Qed.

(* Example proof for prime_fib(1) = 2 *)
Example test_prime_fib_1 : problem_39_spec 1 2.
Proof.
  split.
  - unfold IsPrimeFib. split.
    + apply prime_2.
    + exists 3. apply fib_2.
  - exists []. repeat split.
    + simpl. reflexivity.
    + apply NoDup_nil.
    + intros y. split; intros [].
Qed.

Close Scope nat_scope.