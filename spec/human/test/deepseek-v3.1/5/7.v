Require Import List.
Require Import ZArith.
Require Import Arith.
Require Import Nat.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition problem_5_pre (input output : list Z) : Prop := True.

Definition problem_5_spec (input output : list Z) (d : Z) : Prop :=
  (input = [] -> output = []) /\
  (forall n : nat,
      length input = n -> 1 <= n ->
      length output = 2 * n - 1 /\
      forall i : nat, i < 2 * n - 1 ->
        (Nat.Even i -> nth_error output i = nth_error input (i / 2)) /\
        (Nat.Odd i -> nth_error output i = Some d)
  ).

Example test_intersperse_single : 
  problem_5_spec [10%Z] [10%Z] 5%Z.
Proof.
  unfold problem_5_spec.
  split.
  - intro H1. discriminate.
  - intros n Hlen Hn.
    simpl in Hlen.
    inversion Hlen.
    subst n.
    split.
    + simpl. lia.
    + intros i Hi.
      simpl in Hi.
      assert (i = 0) by lia.
      subst i.
      split.
      * intro H2.
        simpl. reflexivity.
      * intro H3.
        exfalso.
        unfold Nat.Odd in H3.
        destruct H3 as [k H3].
        lia.
Qed.