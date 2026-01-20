Require Import List.
Require Import Arith.
Import ListNotations.

Definition rolling_max_spec (numbers : list nat) (result : list nat) : Prop :=
  length numbers = length result /\
  forall i, i < length numbers ->
            nth i result 0 = fold_left max (firstn (i + 1) numbers) 0.

Example test_rolling_max_empty : rolling_max_spec [] [].
Proof.
  unfold rolling_max_spec.
  split.
  - (* Prove length condition *)
    simpl.
    reflexivity.
  - (* Prove nth element condition *)
    intros i H.
    simpl in H.
    (* H : i < 0, which is impossible for nat *)
    inversion H.
Qed.