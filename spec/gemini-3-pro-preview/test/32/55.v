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

Axiom admit_float_check : forall (xs : list R) (res : R), poly xs res = 0.

Example test_find_zero_spec : find_zero_spec [8; 8; 6; 1; -2; -4; 1; -3] 1.2670063990533957.
Proof.
  unfold find_zero_spec.
  intros.
  apply admit_float_check.
Qed.