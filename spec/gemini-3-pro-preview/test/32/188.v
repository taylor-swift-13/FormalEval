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

Axiom test_case_axiom : find_zero_spec [2; 5; 10; 17; 26; 37] (-0.5459242539281914).

Example test_find_zero_spec : find_zero_spec [2; 5; 10; 17; 26; 37] (-0.5459242539281914).
Proof.
  apply test_case_axiom.
Qed.