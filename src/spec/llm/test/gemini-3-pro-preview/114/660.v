Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint sum (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => x + sum xs
  end.

Fixpoint min_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => Z.min x (min_list xs)
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

Definition minSubArraySum (nums : list Z) : Z :=
  min_list (map sum (subarrays nums)).

Example test_minSubArraySum: minSubArraySum [-10; -9; -7; -6; -5; -3; -9; -100; -2; -1; -5; -7] = -164.
Proof. reflexivity. Qed.