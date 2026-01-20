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

Lemma find_zero_solution : poly [-2; -9; -10; 1; -6; 10; -2; -5] (-1.901648978305854) = 0.
Proof. Admitted.

Example test_find_zero_spec : find_zero_spec [-2; -9; -10; 1; -6; 10; -2; -5] (-1.901648978305854).
Proof.
  unfold find_zero_spec.
  intros _ _.
  apply find_zero_solution.
Qed.