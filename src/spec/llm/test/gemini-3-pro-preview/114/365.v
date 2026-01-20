Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint tails {A} (l : list A) : list (list A) :=
  match l with
  | [] => []
  | x :: xs => (x :: xs) :: tails xs
  end.

Fixpoint inits {A} (l : list A) : list (list A) :=
  match l with
  | [] => []
  | x :: xs => [x] :: map (cons x) (inits xs)
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  let sub_arrays := flat_map inits (tails nums) in
  let sums := map (fold_right Z.add 0) sub_arrays in
  match sums with
  | [] => 0
  | x :: xs => fold_right Z.min x xs
  end.

Example test_minSubArraySum:
  minSubArraySum [1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -100%Z; -1%Z; 1%Z; -50%Z; 1%Z; -1%Z; -3%Z; 1%Z; -1%Z; -1%Z] = -154%Z.
Proof. reflexivity. Qed.