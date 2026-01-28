Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Micromega.Lra.
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

Definition find_zero_spec_approx (xs : list R) (res : R) (eps : R) : Prop :=
  Nat.Even (length xs) ->
  last xs 0 <> 0 ->
  Rabs (poly xs res) < eps.

Example test_find_zero_spec : find_zero_spec_approx [6; 9450000; 9; -6; -7; 2; 6; 1; -4; -10; 6; -11; -1; 9450000; 9; 6] (-6.34920634920635e-07) 1.
Proof.
  unfold find_zero_spec_approx.
  intros.
  simpl.
  lra.
Qed.