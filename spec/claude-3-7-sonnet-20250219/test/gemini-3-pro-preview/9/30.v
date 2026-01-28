Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Fixpoint rolling_max (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
    let fix helper (rem : list Z) (curr : Z) : list Z :=
      match rem with
      | [] => []
      | y :: ys =>
        let m := Z.max curr y in
        m :: helper ys m
      end
    in x :: helper xs x
  end.

Definition rolling_max_spec (numbers result : list Z) : Prop :=
  length result = length numbers /\
  forall i : nat,
    (i < length numbers)%nat ->
    nth i result 0 = fold_left Z.max (firstn (i + 1)%nat numbers) (nth 0%nat numbers 0).

Example test_rolling_max : 
  rolling_max_spec 
    [-1; -2; -3; -4; -4; -2; -1; -4] 
    [-1; -1; -1; -1; -1; -1; -1; -1].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    repeat (destruct i as [|i]; [ simpl; reflexivity | ]).
    simpl in H. lia.
Qed.