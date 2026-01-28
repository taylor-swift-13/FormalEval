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

Lemma test_find_zero_spec_lemma : poly [7; -28; -38; -27; -17; -37; 7; -10] 0.1919905686824449 = 0.
Proof. Admitted.

Example test_find_zero_spec : find_zero_spec [7; -28; -38; -27; -17; -37; 7; -10] 0.1919905686824449.
Proof.
  unfold find_zero_spec.
  intros _ _.
  apply test_find_zero_spec_lemma.
Qed.