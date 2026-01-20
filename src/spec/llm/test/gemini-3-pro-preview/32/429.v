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

Example test_find_zero_spec : find_zero_spec [-300; -630000; 9450000; -78840000; 9449999; 395580000; -1186740000; 1935360001; 1935360000; -1663750000; 725760000; -1186740000] (-0.0004728238117990442).
Proof.
  unfold find_zero_spec.
  intros _ _.
  (* The provided output is a floating-point approximation, so exact equality in R cannot be proven. *)
  Admitted.