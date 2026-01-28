Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

Definition rolling_max_spec (numbers : list nat) (result : list nat) : Prop :=
  length numbers = length result /\
  forall i, i < length numbers ->
            nth i result 0 = fold_left max (firstn (i + 1) numbers) 0.

Example test_rolling_max_empty : rolling_max_spec [] [].
Proof.
  unfold rolling_max_spec.
  split.
  - (* length numbers = length result *)
    simpl.
    reflexivity.
  - (* forall i, i < length numbers -> ... *)
    intros i H.
    simpl in H.
    (* i < 0 is impossible for natural numbers *)
    lia.
Qed.