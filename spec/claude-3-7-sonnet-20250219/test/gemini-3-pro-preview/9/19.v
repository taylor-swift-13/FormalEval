Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition rolling_max_spec (numbers result : list Z) : Prop :=
  length result = length numbers /\
  forall i : nat,
    (i < length numbers)%nat ->
    nth i result 0 = fold_left Z.max (firstn (i + 1)%nat numbers) 0.

Example test_rolling_max_new : rolling_max_spec 
  [0; 4; -3; -4; -5; -4; -3; -2; -1] 
  [0; 4; 4; 4; 4; 4; 4; 4; 4].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    repeat (destruct i as [|i]; [simpl; reflexivity | simpl in H]).
    lia.
Qed.