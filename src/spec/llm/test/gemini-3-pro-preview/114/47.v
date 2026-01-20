Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint initial_segments {A} (l : list A) : list (list A) :=
  match l with
  | [] => []
  | x :: xs => [x] :: map (cons x) (initial_segments xs)
  end.

Fixpoint subarrays {A} (l : list A) : list (list A) :=
  match l with
  | [] => []
  | x :: xs => initial_segments (x :: xs) ++ subarrays xs
  end.

Definition sum (l : list Z) : Z := fold_right Z.add 0 l.

Definition minSubArraySum (nums : list Z) : Z :=
  let subs := subarrays nums in
  let sums := map sum subs in
  match sums with
  | [] => 0
  | x :: xs => fold_right Z.min x xs
  end.

Example test_minSubArraySum: minSubArraySum [-2; -1; -4; 8; -5; -2; 6] = -7.
Proof. reflexivity. Qed.