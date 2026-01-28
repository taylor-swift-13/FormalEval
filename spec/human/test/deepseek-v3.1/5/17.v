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
  problem_5_spec [7%Z] [7%Z] 2%Z.
Proof.
  unfold problem_5_spec.
  split.
  - intro H. discriminate H.
  - intros n Hlen Hn.
    simpl in Hlen.
    assert (n = 1) by lia.
    subst n.
    split.
    + simpl. lia.
    + intros i Hi.
      assert (i < 1) by lia.
      assert (i = 0) by lia.
      subst i.
      split.
      * intro HEven.
        simpl. reflexivity.
      * intro HOdd.
        exfalso.
        unfold Nat.Odd in HOdd.
        destruct HOdd as [k Hk].
        lia.
Qed.