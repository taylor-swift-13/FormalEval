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
  intersperse_spec [4%Z] [4%Z] 4%Z.
Proof.
  unfold intersperse_spec.
  split.
  - intros. discriminate.
  - intros n Hlen Hn.
    destruct n.
    + lia.
    + assert (n = 0) by (simpl in Hlen; lia).
      subst n.
      simpl.
      split.
      * reflexivity.
      * intros i Hi.
        assert (i = 0) by lia.
        subst i.
        split.
        -- intros Heven. apply Nat.even_spec in Heven. inversion Heven. reflexivity.
        -- intros Hodd. apply Nat.odd_spec in Hodd. inversion Hodd.
Qed.