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

Example test_rolling_max_simple : rolling_max_spec [0; 1; 4; 4] [0; 1; 4; 4].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 4 (destruct i as [|i]; [simpl; reflexivity|]).
    simpl in H; lia.
Qed.