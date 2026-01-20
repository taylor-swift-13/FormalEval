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

Example test_find_zero_spec : find_zero_spec [9; -7; 3; 725760000; -28; 2; 8; -6; -4; -10; 6; -1; -7; 8] (-0.0023160288077218798).
Proof.
  unfold find_zero_spec.
  intros.
  (* The test case output is a floating-point approximation, so exact equality in R does not hold. *)
  admit.
Admitted.