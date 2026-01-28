Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint sum (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => x + sum xs
  end.

Fixpoint prefixes (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | x :: xs => [x] :: map (cons x) (prefixes xs)
  end.

Fixpoint subarrays (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | x :: xs => prefixes (x :: xs) ++ subarrays xs
  end.

Definition min_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  min_list (map sum (subarrays nums)).

Example test_case_1 : minSubArraySum [-2; 3; -4; 5; -6; 7; -8; -3; 2; -1; 4] = -11.
Proof. reflexivity. Qed.