Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint prefixes (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | x :: xs => [x] :: map (cons x) (prefixes xs)
  end.

Fixpoint all_subarrays (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | x :: xs => prefixes (x :: xs) ++ all_subarrays xs
  end.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition min_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_right Z.min x xs
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  min_list (map sum_list (all_subarrays nums)).

Example test_minSubArraySum:
  minSubArraySum [21%Z; -1%Z; 1%Z; 1%Z; -1%Z; 0%Z; -1%Z; 1%Z; -1%Z; 1%Z] = -2%Z.
Proof. reflexivity. Qed.