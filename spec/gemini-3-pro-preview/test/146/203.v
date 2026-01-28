Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z :=
  let is_three_digit (n : Z) : bool :=
    let abs_n := Z.abs n in
    (100 <=? abs_n) && (abs_n <=? 999) in
  fold_right (fun x acc => if is_three_digit x then 1 + acc else acc) 0 l.

Example test_case: solution [123; 505; 789; -3; 111] = 4.
Proof.
  reflexivity.
Qed.