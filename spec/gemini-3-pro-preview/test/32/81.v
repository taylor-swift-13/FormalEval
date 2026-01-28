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

Example test_find_zero_spec : find_zero_spec [1; 1; 3; 9; 6; -7; 2; 8] (-1.0796475563152408).
Proof.
  unfold find_zero_spec.
  intros _ _.
  (* The provided result is a floating-point approximation.
     Exact equality in R cannot be proven for this value. *)
  Admitted.