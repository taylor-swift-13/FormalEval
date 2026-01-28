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

Example test_find_zero_spec : find_zero_spec [9; -6; 395580000; 0; -78840000; 3; 2; 7; -78840000; 8; -10; 6; 5; -1; 2; 3; 9; -1; -10; 2] 1.2321504478116667.
Proof.
  unfold find_zero_spec.
  intros.
  admit.
Admitted.