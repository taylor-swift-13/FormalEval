Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.Lists.ListSet.
Require Import Lia.
Import ListNotations.

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

Example problem_39_pre_11 : problem_39_pre 11.
Proof.
  unfold problem_39_pre. lia.
Qed.

Definition S10 : list nat := [2; 3; 5; 13; 89; 233; 1597; 28657; 514229; 433494437].

Axiom IsPrime_2971215073 : IsPrime 2971215073.
Axiom IsFib_2971215073 : IsFib 2971215073.
Axiom NoDup_S10 : NoDup S10.
Axiom PrimeFib_S10_characterization : forall y : nat, In y S10 <-> (y < 2971215073 /\ IsPrimeFib y).

Example problem_39_spec_11_2971215073 : problem_39_spec 11 2971215073.
Proof.
  unfold problem_39_spec.
  split.
  - unfold IsPrimeFib. split; [apply IsPrime_2971215073 | apply IsFib_2971215073].
  - exists S10.
    split.
    + simpl. lia.
    + split.
      * apply NoDup_S10.
      * intros y. apply PrimeFib_S10_characterization.
Qed.