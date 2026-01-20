Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope bool_scope.

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
  double_the_difference_spec [13%Z; 10%Z; 3%Z; 5%Z; 7%Z; 11%Z; 13%Z; 14%Z; 17%Z; 14%Z; 19%Z] 1192%Z.
Proof.
  unfold double_the_difference_spec.
  simpl.
  reflexivity.
Qed.