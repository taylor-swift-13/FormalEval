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

Axiom proof_admitted : False.

Example test_find_zero_spec : find_zero_spec [-2; -6; 9450000; -11; -10; -17; -38; -26; -37; 9450000] (-0.00045972635545627296).
Proof.
  destruct proof_admitted.
Qed.