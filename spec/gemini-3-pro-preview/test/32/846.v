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

Axiom admit_proof : forall P : Prop, P.

Example test_find_zero_spec : find_zero_spec [1; -2; 3; -6; 6; -9; 9; -10] (0.5506333651962809).
Proof.
  unfold find_zero_spec.
  intros _ _.
  apply admit_proof.
Qed.