Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i, (i < length numbers)%nat ->
            nth i result 0 = fold_left Z.max (firstn (S i) numbers) (nth 0%nat numbers 0).

Example test_rolling_max_1 : 
  rolling_max_spec [4; 4; -4; -5; -4; -2; -1; -2; -5; -2] 
                   [4; 4; 4; 4; 4; 4; 4; 4; 4; 4].
Proof.
  unfold rolling_max_spec.
  split.
  - (* length numbers = length result *)
    simpl.
    reflexivity.
  - (* forall i, i < length numbers -> ... *)
    intros i H.
    repeat (destruct i; [ simpl; reflexivity | ]).
    (* i >= 10, contradiction with H *)
    simpl in H.
    lia.
Qed.