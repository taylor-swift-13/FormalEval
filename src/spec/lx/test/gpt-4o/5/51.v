Require Import List.
Require Import ZArith.
Require Import Arith.
Require Import Nat.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition intersperse_pre (input output : list Z) : Prop := True.

Definition intersperse_spec (input output : list Z) (d : Z) : Prop :=
  (input = [] -> output = []) /\
  (forall n : nat,
      length input = n -> 1 <= n ->
      length output = 2 * n - 1 /\
      forall i : nat, i < 2 * n - 1 ->
        (Nat.Even i -> nth_error output i = nth_error input (i / 2)) /\
        (Nat.Odd i -> nth_error output i = Some d)
  ).

Example intersperse_test_case :
  intersperse_spec [-2; 3; 4]%Z [-2; -8; 3; -8; 4]%Z (-8)%Z.
Proof.
  unfold intersperse_spec.
  split.
  - intros. discriminate.
  - intros n Hlen Hn.
    simpl in Hlen. inversion Hlen as [Hlen'].
    split.
    + simpl. lia.
    + intros i Hi.
      assert (Hn': n = 3) by lia.
      rewrite Hn' in *.
      destruct i.
      * simpl. split; [reflexivity|].
        intros Hodd. exfalso. apply Nat.odd_spec in Hodd. inversion Hodd.
      * destruct i.
        -- simpl. split; [|reflexivity].
           intros Heven. exfalso. apply Nat.even_spec in Heven. inversion Heven.
        -- destruct i.
           ++ simpl. split; [reflexivity|].
              intros Hodd. exfalso. apply Nat.odd_spec in Hodd. inversion Hodd.
           ++ destruct i.
              ** simpl. split; [|reflexivity].
                 intros Heven. exfalso. apply Nat.even_spec in Heven. inversion Heven.
              ** destruct i.
                 --- simpl. split; [reflexivity|].
                     intros Hodd. exfalso. apply Nat.odd_spec in Hodd. inversion Hodd.
                 --- lia.
Qed.