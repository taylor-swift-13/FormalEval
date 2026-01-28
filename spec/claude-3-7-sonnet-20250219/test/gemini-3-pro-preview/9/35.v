Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

Fixpoint prefix_max (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs =>
    match prefix_max xs with
    | [] => [x]
    | y :: ys =>
      let m := Nat.max x y in
      m :: ys
    end
  end.

Definition rolling_max_spec (numbers result : list nat) : Prop :=
  length result = length numbers /\
  forall i,
    i < length numbers ->
    nth i result 0 = fold_left Nat.max (firstn (i + 1) numbers) 0.

Example test_rolling_max_basic : rolling_max_spec [10; 20; 30; 40; 50; 50] [10; 20; 30; 40; 50; 50].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 6 (destruct i; [simpl; reflexivity |]).
    simpl in H. lia.
Qed.