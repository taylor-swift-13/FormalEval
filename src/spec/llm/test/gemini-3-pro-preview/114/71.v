Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  let fix prefixes (l : list Z) : list (list Z) :=
    match l with
    | [] => []
    | x :: xs => [x] :: map (cons x) (prefixes xs)
    end in
  let fix sublists (l : list Z) : list (list Z) :=
    match l with
    | [] => []
    | x :: xs => prefixes (x :: xs) ++ sublists xs
    end in
  let sums := map (fold_right Z.add 0) (sublists nums) in
  match sums with
  | [] => 0
  | y :: ys => fold_right Z.min y ys
  end.

Example test_minSubArraySum: minSubArraySum [-3%Z; -2%Z; -3%Z; 4%Z; -4%Z] = -8%Z.
Proof. reflexivity. Qed.