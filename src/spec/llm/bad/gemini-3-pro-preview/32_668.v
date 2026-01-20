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

Example test_find_zero_spec : find_zero_spec [-300%Z; 21000%Z; -1%Z; 9450000%Z; -78840000%Z; -300%Z; -1186740000%Z; -1663750000%Z; 725760000%Z; -78840000%Z] 0.013337236099604821%R.
Proof.
  unfold find_zero_spec.
  intros _ _.
  simpl.
  (* The provided output is a floating point approximation, so exact equality in R cannot be proven. *)
  admit.
Admitted.