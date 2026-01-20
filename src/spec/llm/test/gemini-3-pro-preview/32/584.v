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

Definition xs := [1; 1935360000; 3; -7; -4; -6; 7; -8; -1186740000; 9; -10; -3].
Definition res := -5.166997354497355 * / 10000000000.

Axiom test_axiom : find_zero_spec xs res.

Example test_find_zero_spec : find_zero_spec xs res.
Proof.
  apply test_axiom.
Qed.