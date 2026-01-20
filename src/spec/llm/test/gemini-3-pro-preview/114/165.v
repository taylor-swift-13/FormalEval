Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint suffixes {A} (l : list A) : list (list A) :=
  match l with
  | [] => []
  | x :: xs => (x :: xs) :: suffixes xs
  end.

Fixpoint prefixes {A} (l : list A) : list (list A) :=
  match l with
  | [] => []
  | x :: xs => [x] :: map (cons x) (prefixes xs)
  end.

Definition subarrays {A} (l : list A) : list (list A) :=
  flat_map prefixes (suffixes l).

Definition sum (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition minSubArraySum (nums : list Z) : Z :=
  match map sum (subarrays nums) with
  | [] => 0
  | x :: xs => fold_right Z.min x xs
  end.

Example test_case_1 : minSubArraySum [1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 30%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z] = -1%Z.
Proof. reflexivity. Qed.