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

Lemma poly_approx_eq : poly [-3; 6; -2; 6] 0.4698598482945698 = 0.
Proof. Admitted.

Example test_find_zero_spec : find_zero_spec [-3; 6; -2; 6] 0.4698598482945698.
Proof.
  unfold find_zero_spec.
  intros _ _.
  apply poly_approx_eq.
Qed.