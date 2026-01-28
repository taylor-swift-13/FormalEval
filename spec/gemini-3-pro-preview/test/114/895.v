Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

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

Definition sum_list (l : list Z) : Z := fold_right Z.add 0 l.

Definition minSubArraySum (nums : list Z) : Z :=
  match map sum_list (subarrays nums) with
  | [] => 0
  | x :: xs => fold_right Z.min x xs
  end.

Example test_minSubArraySum:
  minSubArraySum [-10%Z; -9%Z; -7%Z; -6%Z; -5%Z; -9%Z; -9%Z; -100%Z; -2%Z; -1%Z] = -158%Z.
Proof.
  compute. reflexivity.
Qed.