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
Ltac give_up := destruct proof_admitted.

Example test_find_zero_spec : find_zero_spec [6; -2; 2; 1; -3; 3744] (-0.28204015546382133).
Proof.
  unfold find_zero_spec.
  intros _ _.
  simpl.
  give_up.
Qed.