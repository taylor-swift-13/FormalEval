Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition compare_spec (game guess out : list Z) : Prop :=
  List.length game = List.length guess /\
  out = List.map (fun p => match p with (a, b) => Z.abs (Z.sub a b) end) (List.combine game guess).

Example test_compare :
  compare_spec (1 :: 2 :: 3 :: 4 :: 5 :: 1 :: nil) (1 :: 2 :: 3 :: 4 :: 2 :: (-2) :: nil) (0 :: 0 :: 0 :: 0 :: 3 :: 3 :: nil).
Proof.
  unfold compare_spec.
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.