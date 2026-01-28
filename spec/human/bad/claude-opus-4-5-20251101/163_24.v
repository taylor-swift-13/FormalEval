Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Lists.SetoidList.
Require Import Lia.
Import ListNotations.

Definition problem_163_pre (a b : nat) : Prop := a > 0 /\ b > 0.

Definition problem_163_spec (a b : nat) (l : list nat) : Prop :=
  (forall d : nat,
    In d l <-> (min a b <= d /\ d <= max a b /\ d < 10 /\ Nat.Even d)) /\
  Sorted le l /\
  NoDup l.

Example test_generate_integers_201_9 :
  problem_163_spec 201 9 [].
Proof.
  unfold problem_163_spec.
  split; [| split].
  - intros d.
    simpl.
    split.
    + intros H. contradiction.
    + intros (Hmin & Hmax & Hlt10 & Heven).
      simpl in Hmin, Hmax.
      lia.
  - constructor.
  - constructor.
Qed.