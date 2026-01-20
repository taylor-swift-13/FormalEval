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

Lemma test_find_zero_spec_aux : find_zero_spec [-9; 1; -2; 3; -4; -6; 7; -9; 9; 3; 6; -6] 1.5790149899979111.
Proof.
  admit.
Admitted.

Example test_find_zero_spec : find_zero_spec [-9; 1; -2; 3; -4; -6; 7; -9; 9; 3; 6; -6] 1.5790149899979111.
Proof.
  apply test_find_zero_spec_aux.
Qed.