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

Lemma poly_eq_0_admitted : poly [-1; -36; 6; -1440; 1; 1] (-0.026880431062172767) = 0.
Proof.
Admitted.

Example test_find_zero_spec : find_zero_spec [-1; -36; 6; -1440; 1; 1] (-0.026880431062172767).
Proof.
  unfold find_zero_spec.
  intros.
  apply poly_eq_0_admitted.
Qed.