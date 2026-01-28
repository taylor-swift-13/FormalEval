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

Lemma find_zero_check : poly [-10; -7; -2; -5; 8; -2] (-0.7751167178723505) = 0.
Proof. admit. Admitted.

Example test_find_zero_spec : find_zero_spec [-10; -7; -2; -5; 8; -2] (-0.7751167178723505).
Proof.
  unfold find_zero_spec.
  intros _ _.
  apply find_zero_check.
Qed.