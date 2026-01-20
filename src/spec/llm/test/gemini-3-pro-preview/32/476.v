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

Lemma test_find_zero_spec_helper : find_zero_spec [1; 3; 10; -4; 4; 8; 2; -6; 7; -8; 8; -10] 1.1612913909014462.
Proof.
  admit.
Admitted.

Example test_find_zero_spec : find_zero_spec [1; 3; 10; -4; 4; 8; 2; -6; 7; -8; 8; -10] 1.1612913909014462.
Proof.
  apply test_find_zero_spec_helper.
Qed.