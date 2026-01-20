Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint sum_sq_odd (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t =>
    if (Z.leb 0 h) && (Z.odd h)
    then h * h + sum_sq_odd t
    else sum_sq_odd t
  end.

Definition double_the_difference_spec (l : list Z) (res : Z) : Prop :=
  res = sum_sq_odd l.

Example double_the_difference_test :
  double_the_difference_spec [7%Z; -11%Z; -14%Z; -16%Z; 19%Z; 24%Z; 25%Z; 26%Z; -28%Z; -29%Z; -28%Z; -16%Z] 1035%Z.
Proof.
  unfold double_the_difference_spec.
  simpl.
  reflexivity.
Qed.