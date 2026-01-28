Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.max xs x
  end.

Definition rolling_max_spec (numbers result : list Z) : Prop :=
  length result = length numbers /\
  forall i,
    (i < length numbers)%nat ->
    nth i result 0 = max_list (firstn (S i) numbers).

Example test_rolling_max_neg : 
  rolling_max_spec 
    [-1; -2; -3; -4; -5; -4; -3; -2; -1] 
    [-1; -1; -1; -1; -1; -1; -1; -1; -1].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    repeat (destruct i as [|i]; [ simpl; reflexivity | ]).
    simpl in H. lia.
Qed.