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

Example test_rolling_max_simple : rolling_max_spec [3%Z; 2%Z; 3%Z; 100%Z; 3%Z] [3%Z; 3%Z; 3%Z; 100%Z; 100%Z].
Proof.
  unfold rolling_max_spec.
  split.
  - (* Check length equality *)
    reflexivity.
  - (* Check element-wise equality *)
    intros i H.
    do 5 (destruct i; [ vm_compute; reflexivity | ]).
    (* Handle out of bounds indices *)
    simpl in H; lia.
Qed.