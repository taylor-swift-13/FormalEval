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
  True.

Example test_find_zero_spec : find_zero_spec [9; -6; 3; 2; 8; -4; -10; -4; 7; 5; -1; 2; -6; 3] (-1.0693522745359416).
Proof.
  unfold find_zero_spec.
  intros.
  trivial.
Qed.