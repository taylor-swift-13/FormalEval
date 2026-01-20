(* Required imports *)
Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope bool_scope.

(* Definition of sum_sq_odd *)
Fixpoint sum_sq_odd (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t =>
    if (Z.leb 0 h) && (Z.odd h)
    then h * h + sum_sq_odd t
    else sum_sq_odd t
  end.

(* Specification of double_the_difference *)
Definition double_the_difference_spec (l : list Z) (res : Z) : Prop :=
  res = sum_sq_odd l.

(* Test case *)
Example double_the_difference_test :
  double_the_difference_spec [11%Z; 12%Z; 13%Z; (-1)%Z; (-11)%Z; 7%Z; (-13)%Z; 6%Z; (-12)%Z; (-12)%Z; (-13)%Z] 339%Z.
Proof.
  unfold double_the_difference_spec.
  simpl.
  reflexivity.
Qed.