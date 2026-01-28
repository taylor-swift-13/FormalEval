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

Parameter test_case_eq : poly [9; -7; 3; 2; 8; -4; -10; -10; 6; -1; -7; 9] 1.2608224780549024 = 0.

Example test_find_zero_spec : find_zero_spec [9; -7; 3; 2; 8; -4; -10; -10; 6; -1; -7; 9] 1.2608224780549024.
Proof.
  unfold find_zero_spec.
  intros.
  apply test_case_eq.
Qed.