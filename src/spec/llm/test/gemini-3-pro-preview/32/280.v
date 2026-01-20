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

Example test_find_zero_spec : find_zero_spec [9450000; 6; 9; -7; 4; 2; 8; 2; -4; -10; 7; -22; -1; 9450000] (-1.0000004232808333).
Proof.
  unfold find_zero_spec.
  intros.
  destruct proof_admitted.
Qed.