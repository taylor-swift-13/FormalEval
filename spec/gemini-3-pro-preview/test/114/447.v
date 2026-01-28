Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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

Definition sum (l : list Z) : Z := fold_left Z.add l 0.

Definition min_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  min_list (map sum (all_subarrays nums)).

Example test_minSubArraySum: minSubArraySum [1; -2; -4; 5; -6; -8; 9; -10; -10; 5] = -26.
Proof. vm_compute. reflexivity. Qed.