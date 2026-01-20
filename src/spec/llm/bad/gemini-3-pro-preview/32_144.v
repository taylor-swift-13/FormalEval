Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lra.
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

Example test_find_zero_spec : find_zero_spec [1; -20; 156; -864; 2667; -4392; 3743; -1440] 0.08765104090435215.
Proof.
  unfold find_zero_spec.
  intros _ _.
  simpl.
  lra.
Qed.