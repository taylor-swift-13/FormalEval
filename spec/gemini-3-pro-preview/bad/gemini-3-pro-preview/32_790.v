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

Example test_find_zero_spec : find_zero_spec [-300%Z; 21000%Z; 11%Z; -78840000%Z; 395580000%Z; -1186740000%Z; 1935360000%Z; -1663750000%Z; 9450000%Z; -630000%Z] (-0.020248698321712253).
Proof.
  unfold find_zero_spec.
  intros _ _.
  simpl.
  field.
Qed.