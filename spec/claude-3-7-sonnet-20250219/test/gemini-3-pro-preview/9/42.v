Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Fixpoint rolling_max_go (max_so_far : Z) (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
    let new_max := Z.max max_so_far x in
    new_max :: rolling_max_go new_max xs
  end.

Definition rolling_max (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => x :: rolling_max_go x xs
  end.

Definition rolling_max_spec (numbers result : list Z) : Prop :=
  length result = length numbers /\
  forall i : nat,
    (i < length numbers)%nat ->
    nth i result 0 = fold_left Z.max (firstn (i + 1)%nat numbers) (nth 0%nat numbers 0).

Example test_rolling_max_custom : 
  rolling_max_spec [1; 2; -3; 4; 5; 4; 3; 2; 1] [1; 2; 2; 4; 5; 5; 5; 5; 5].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 9 (destruct i; [ simpl; reflexivity | ]).
    simpl in H. lia.
Qed.