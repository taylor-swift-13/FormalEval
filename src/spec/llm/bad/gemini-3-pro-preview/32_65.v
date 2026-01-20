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

Example test_find_zero_spec : find_zero_spec [-2; -1; 9; -4] ((1 - sqrt 17) / 8).
Proof.
  unfold find_zero_spec.
  intros _ _.
  simpl.
  set (x := (1 - sqrt 17) / 8).
  replace (-2 + x * (-1 + x * (9 + x * -4))) with ((2 - x) * (4 * x * x - x - 1)) by ring.
  replace (4 * x * x - x - 1) with 0.
  - ring.
  - unfold x.
    field_simplify.
    replace (sqrt 17 * sqrt 17) with 17 by (apply sqrt_sqrt; lra).
    field.
Qed.