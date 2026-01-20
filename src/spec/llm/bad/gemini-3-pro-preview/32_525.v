Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Micromega.Lra.
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

Example test_find_zero_spec : find_zero_spec [-300; 21000; -630000; 9450000; -78840000; -300; -1186740000; -1663750000; 725760000; -78840000] (-0.6505040365341035).
Proof.
  unfold find_zero_spec.
  intros _ _.
  simpl.
  lra.
Qed.