Require Import List.
Require Import Arith.

Definition rolling_max_spec (numbers : list nat) (result : list nat) : Prop :=
  length numbers = length result /\
  forall i, i < length numbers ->
            nth i result 0 = fold_left max (firstn (i + 1) numbers) 0.

Example rolling_max_empty : rolling_max_spec nil nil.
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H. simpl in H. inversion H.
Qed.