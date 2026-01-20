Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  let fix tails (l : list Z) : list (list Z) :=
    match l with
    | [] => []
    | x :: xs => (x :: xs) :: tails xs
    end in
  let fix inits (l : list Z) : list (list Z) :=
    match l with
    | [] => []
    | x :: xs => [x] :: map (cons x) (inits xs)
    end in
  let subarrays := flat_map inits (tails nums) in
  let sums := map (fold_right Z.add 0) subarrays in
  match sums with
  | [] => 0
  | x :: xs => fold_right Z.min x xs
  end.

Example test_case_1 : minSubArraySum [-1%Z; 2%Z; -3%Z; 4%Z; -6%Z; 6%Z; -7%Z; 8%Z; -9%Z; 10%Z] = -9%Z.
Proof. reflexivity. Qed.