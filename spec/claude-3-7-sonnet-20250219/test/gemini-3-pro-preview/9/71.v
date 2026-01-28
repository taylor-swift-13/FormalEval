Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition rolling_max_spec (numbers result : list Z) : Prop :=
  length result = length numbers /\
  forall i,
    (i < length numbers)%nat ->
    nth i result 0 = 
      match firstn (i + 1) numbers with
      | [] => 0
      | x :: xs => fold_left Z.max xs x
      end.

Example test_rolling_max : rolling_max_spec [2; 2; -3; 4; 5; 4; 3; 2; 1; 2] [2; 2; 2; 4; 5; 5; 5; 5; 5; 5].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 10 (destruct i; [simpl; reflexivity | ]).
    simpl in H. lia.
Qed.