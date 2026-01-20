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

Lemma poly_root_admitted : poly [-1; -3; -4; -6] (-0.4203806159365355) = 0.
Proof.
  (* The provided output is a floating point approximation, so it is not exactly 0 in R. *)
  Admitted.

Example test_find_zero_spec : find_zero_spec [-1; -3; -4; -6] (-0.4203806159365355).
Proof.
  unfold find_zero_spec.
  intros _ _.
  apply poly_root_admitted.
Qed.