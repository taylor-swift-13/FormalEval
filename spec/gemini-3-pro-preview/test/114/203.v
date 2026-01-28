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

Definition sum_list (l : list Z) : Z := fold_right Z.add 0 l.

Definition minSubArraySum (nums : list Z) : Z :=
  match map sum_list (all_subarrays nums) with
  | [] => 0
  | x :: xs => fold_right Z.min x xs
  end.

Example test_minSubArraySum:
  minSubArraySum [-100%Z; -10%Z; -50%Z; 100%Z; 50%Z; -50%Z; 100%Z; -100%Z; -50%Z; 100%Z; 99%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; -100000%Z; 50%Z; -51%Z; 100%Z] = -100101%Z.
Proof. vm_compute. reflexivity. Qed.