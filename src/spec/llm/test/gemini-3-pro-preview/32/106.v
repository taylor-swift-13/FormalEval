Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
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

Axiom check_test_case : find_zero_spec [-1; 10; 1; 1] (IZR 9892473118279571%Z / IZR 100000000000000000%Z).

Example test_find_zero_spec : find_zero_spec [-1; 10; 1; 1] (IZR 9892473118279571%Z / IZR 100000000000000000%Z).
Proof.
  apply check_test_case.
Qed.