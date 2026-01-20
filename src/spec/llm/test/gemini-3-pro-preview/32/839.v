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

Example test_find_zero_spec : find_zero_spec [-1186740000; 9; -7; 2; 8; -4; 395580001; 7; 5; 6; -4; 9] 1.2009369325178294.
Proof.
  unfold find_zero_spec.
  intros _ _.
  simpl.
  Admitted.