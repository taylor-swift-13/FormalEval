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

Axiom test_find_zero_admitted : find_zero_spec [1; 3; 5; -6; 7; -8; -10; 5] 0.9123136001758723.

Example test_find_zero_spec : find_zero_spec [1; 3; 5; -6; 7; -8; -10; 5] 0.9123136001758723.
Proof.
  apply test_find_zero_admitted.
Qed.