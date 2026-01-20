Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint prefixes {A} (l : list A) : list (list A) :=
  match l with
  | [] => []
  | x :: xs => [x] :: (map (cons x) (prefixes xs))
  end.

Fixpoint suffixes {A} (l : list A) : list (list A) :=
  match l with
  | [] => []
  | x :: xs => (x :: xs) :: suffixes xs
  end.

Definition subarrays {A} (l : list A) : list (list A) :=
  flat_map prefixes (suffixes l).

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition min_list (l : list Z) : Z :=
  match l with
  | [] => 0 
  | x :: xs => fold_right Z.min x xs
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  min_list (map sum_list (subarrays nums)).

Example test_minSubArraySum: minSubArraySum [0; -7; -2; -3; -4] = -16.
Proof. reflexivity. Qed.