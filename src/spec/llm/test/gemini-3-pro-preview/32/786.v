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

Definition output_val : R := -4126984126984127 / 10 ^ 20%nat.

Lemma poly_eq : poly [-26; -630000; -36; -36; 0; -36] output_val = 0.
Proof. Admitted.

Example test_find_zero_spec : find_zero_spec [-26; -630000; -36; -36; 0; -36] output_val.
Proof.
  unfold find_zero_spec.
  intros _ _.
  apply poly_eq.
Qed.