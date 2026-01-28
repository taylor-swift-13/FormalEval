Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.

Definition max_prefix_at (numbers : list Z) (i : nat) : option Z :=
  match firstn (S i) numbers with
  | [] => None
  | x :: xs => Some (List.fold_left Z.max xs x)
  end.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length result = length numbers /\
  forall i, i < length numbers ->
    nth_error result i = max_prefix_at numbers i.

Example test_rolling_max_basic : rolling_max_spec [0%Z; 1%Z; 4%Z; 4%Z] [0%Z; 1%Z; 4%Z; 4%Z].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl.
    reflexivity.
  - intros i H.
    repeat (destruct i as [|i]; [simpl; reflexivity | ]).
    simpl in H.
    lia.
Qed.