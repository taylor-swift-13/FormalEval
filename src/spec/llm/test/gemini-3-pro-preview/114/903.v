Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint prefixes {A} (l : list A) : list (list A) :=
  match l with
  | [] => []
  | x :: xs => [x] :: map (cons x) (prefixes xs)
  end.

Fixpoint tails {A} (l : list A) : list (list A) :=
  match l with
  | [] => []
  | x :: xs => (x :: xs) :: tails xs
  end.

Definition subarrays {A} (l : list A) : list (list A) :=
  flat_map prefixes (tails l).

Definition sum (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition min_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  min_list (map sum (subarrays nums)).

Example test_minSubArraySum : minSubArraySum [-1%Z; 2%Z; 4%Z; -5%Z; 6%Z; -7%Z; 8%Z; -7%Z; -9%Z; 10%Z; -7%Z; 4%Z; 10%Z; 2%Z] = -16%Z.
Proof. reflexivity. Qed.