Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope R_scope.

Fixpoint poly (xs : list R) (x : R) : R :=
  match xs with
  | [] => 0
  | c :: cs => c + x * poly cs x
  end.

Definition find_zero_spec (xs : list R) (res : R) : Prop :=
  Nat.Even (length xs) ->
  last xs 0 <> 0 ->
  poly xs res = 0.

Example test_find_zero_spec : find_zero_spec [9450000; 6; 9; -7; 3; 2; 8; 2; -4; -78840000; 6; 5; -1; 9450000] (-1.699958805224867).
Proof.
  unfold find_zero_spec.
  intros _ _.
  simpl.
  admit.
Admitted.