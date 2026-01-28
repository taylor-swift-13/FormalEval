Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint sum (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => h + sum t
  end.

Fixpoint prefixes (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | h :: t => [h] :: map (cons h) (prefixes t)
  end.

Fixpoint tails (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | h :: t => (h :: t) :: tails t
  end.

Definition all_subarrays (l : list Z) : list (list Z) :=
  flat_map prefixes (tails l).

Fixpoint min_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => Z.min x (min_list xs)
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  min_list (map sum (all_subarrays nums)).

Example test_minSubArraySum: minSubArraySum [2%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; -8%Z; 1%Z; -1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z] = -10%Z.
Proof. reflexivity. Qed.