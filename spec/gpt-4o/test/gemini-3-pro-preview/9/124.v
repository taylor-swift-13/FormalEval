Require Import List.
Require Import Arith.
Require Import Lia.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i : nat, (i < length numbers)%nat ->
            nth i result 0 = 
            let p := firstn (i + 1) numbers in
            fold_left Z.max (tl p) (hd 0 p).

Example test_rolling_max : 
  rolling_max_spec 
    [-10; -5; -3; -4; 70; -8; -11; -15; 20; 0; 5] 
    [-10; -5; -3; -3; 70; 70; 70; 70; 70; 70; 70].
Proof.
  unfold rolling_max_spec.
  split.
  - (* length numbers = length result *)
    simpl.
    reflexivity.
  - (* forall i, i < length numbers -> ... *)
    intros i H.
    repeat (destruct i as [|i]; [
      simpl; reflexivity |
      simpl in H
    ]).
    lia.
Qed.