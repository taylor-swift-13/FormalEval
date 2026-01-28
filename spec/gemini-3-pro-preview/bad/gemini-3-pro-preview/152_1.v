Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition compare_spec (game guess result : list Z) : Prop :=
  length game = length guess /\
  length result = length game /\
  (forall i : nat, (i < length game)%nat ->
    nth i result 0 = Z.abs (nth i game 0 - nth i guess 0)).

Example test_compare_proof:
  compare_spec 
    [1; 2; 3; 4; 5; 1] 
    [1; 2; 3; 4; 2; -2] 
    [0; 0; 0; 0; 3; 3].
Proof.
  unfold compare_spec.
  repeat split.
  - (* Check length game = length guess *)
    simpl. reflexivity.
  - (* Check length result = length game *)
    simpl. reflexivity.
  - (* Check element-wise condition *)
    intros i Hi.
    simpl in Hi.
    (* Perform case analysis on the index i for all valid positions (0 to 5) *)
    destruct i as [|i].
    { simpl. reflexivity. } (* i = 0 *)
    destruct i as [|i].
    { simpl. reflexivity. } (* i = 1 *)
    destruct i as [|i].
    { simpl. reflexivity. } (* i = 2 *)
    destruct i as [|i].
    { simpl. reflexivity. } (* i = 3 *)
    destruct i as [|i].
    { simpl. reflexivity. } (* i = 4 *)
    destruct i as [|i].
    { simpl. reflexivity. } (* i = 5 *)
    (* For i >= 6, the hypothesis Hi (i < 6) is false *)
    lia.
Qed.