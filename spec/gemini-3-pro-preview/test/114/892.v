Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z :=
  let is_unique x := (count_occ Z.eq_dec l x =? 1)%nat in
  let uniques := filter is_unique l in
  match uniques with
  | [] => 0
  | h :: t => fold_right Z.min h t
  end.

Example test_case: solution [-8%Z; -9%Z; 20%Z; -30%Z; 40%Z; -50%Z; 60%Z; 80%Z; -9%Z; -70%Z; 80%Z; -90%Z; 100%Z] = -90%Z.
Proof. compute. reflexivity. Qed.