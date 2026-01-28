Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition min_Z (a b : Z) : Z := if a <? b then a else b.

Fixpoint sum (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => h + sum t
  end.

Fixpoint prefixes (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | x :: xs => [x] :: map (cons x) (prefixes xs)
  end.

Fixpoint tails (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | x :: xs => (x :: xs) :: tails xs
  end.

Definition subarrays (l : list Z) : list (list Z) :=
  flat_map prefixes (tails l).

Fixpoint min_list_aux (a : Z) (l : list Z) : Z :=
  match l with
  | [] => a
  | x :: xs => min_list_aux (min_Z a x) xs
  end.

Definition min_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => min_list_aux x xs
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  min_list (map sum (subarrays nums)).

Example example_test_case : minSubArraySum [1%Z; -2%Z; -2%Z; 3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; -10%Z; 7%Z; -2%Z; 7%Z; 7%Z] = -10%Z.
Proof.
  compute. reflexivity.
Qed.