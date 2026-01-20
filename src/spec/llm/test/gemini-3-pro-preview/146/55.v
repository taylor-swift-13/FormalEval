Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_aux (fuel : nat) (z : Z) : Z :=
  match fuel with
  | O => z
  | S f => if z <? 10 then z else get_first_aux f (z / 10)
  end.

Definition get_first (z : Z) : Z :=
  let z' := Z.abs z in
  get_first_aux (Z.to_nat z') z'.

Definition solve (nums : list Z) : Z :=
  let predicate (x : Z) :=
    let abs_x := Z.abs x in
    (abs_x >=? 10) && (get_first x =? (abs_x mod 10)) in
  fold_right (fun x acc => if predicate x then x + acc else acc) 0 nums.

Example test_case_new : solve [24; -25; 9; -91; -67; -71; -91; -71; -18] = 0.
Proof. reflexivity. Qed.