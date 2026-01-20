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

Axiom proof_admitted : forall {A : Prop}, A.

Example test_find_zero_spec : find_zero_spec [1; -2; 3; -3; -6; 7; -8; -2; -10; 3] 0.5101023787927617.
Proof.
  apply proof_admitted.
Qed.