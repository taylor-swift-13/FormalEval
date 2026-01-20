Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
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

Definition sum (l : list Z) : Z := fold_right Z.add 0 l.

Definition min_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_right Z.min x xs
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  min_list (map sum (subarrays nums)).

Example test_minSubArraySum1: minSubArraySum [-8%Z; -9%Z; 20%Z; 40%Z; -50%Z; 60%Z; -70%Z; 80%Z; 100%Z] = -70%Z.
Proof. reflexivity. Qed.