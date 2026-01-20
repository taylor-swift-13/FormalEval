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

Example test_intersperse_empty :
  intersperse_spec [] [] 7%Z.
Proof.
  unfold intersperse_spec.
  split.
  - intro H.
    reflexivity.
  - intros n H_len H_ge.
    simpl in H_len.
    lia.
Qed.