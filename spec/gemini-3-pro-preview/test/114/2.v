Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint prefixes {A} (l : list A) : list (list A) :=
  match l with
  | [] => []
  | x :: xs => [x] :: map (cons x) (prefixes xs)
  end.

Fixpoint subarrays {A} (l : list A) : list (list A) :=
  match l with
  | [] => []
  | x :: xs => prefixes (x :: xs) ++ subarrays xs
  end.

Definition sum (l : list Z) : Z := fold_right Z.add 0 l.

Definition min_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_right Z.min x xs
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  min_list (map sum (subarrays nums)).

Example test_case : minSubArraySum [-1%Z; -2%Z; -3%Z] = -6%Z.
Proof. reflexivity. Qed.