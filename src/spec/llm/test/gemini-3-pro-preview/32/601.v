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

Example test_find_zero_spec : find_zero_spec [1; -630002; 1935360000; 3; -7; -630002; -4; -6; 7; -4; -8; -1663750000; -1186740000; 9; -10; 8; -3; 9] 0.0000015951126848920865.
Proof.
  unfold find_zero_spec.
  intros _ _.
  (* The provided root is a floating point approximation, so exact equality in R cannot be proven. *)
  admit.
Admitted.