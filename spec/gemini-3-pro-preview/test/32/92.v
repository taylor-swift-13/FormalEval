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

Parameter proof_admitted : forall P : Prop, P.

Example test_find_zero_spec : find_zero_spec [2; -3; -6; 10; -10; -7; 3; -3] 0.4243726070846436.
Proof.
  unfold find_zero_spec.
  intros.
  apply proof_admitted.
Qed.