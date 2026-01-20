Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [0; 1; 1; 1; 0; 9; 0; 1; -1] [1; 2; 3; 0; 45; 0; 7; -8].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    (* We use 'do' to destruct the index 8 times corresponding to the result list length.
       This avoids large proof terms or timeouts associated with complex simplifications. *)
    do 8 (destruct i as [|i]; [ simpl; reflexivity | ]).
    (* The remaining case implies i >= 8, which contradicts H *)
    lia.
Qed.