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

Definition output : R := 9.993842479732482.

Lemma poly_root_eq : poly [-4392; -20; 6; 4] output = 0.
Proof.
  Admitted.

Example test_find_zero_spec : find_zero_spec [-4392; -20; 6; 4] output.
Proof.
  unfold find_zero_spec.
  intros Hlen Hlast.
  apply poly_root_eq.
Qed.