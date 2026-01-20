Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition min (a b : Z) : Z := if a <? b then a else b.

Fixpoint sum (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => x + sum xs
  end.

Fixpoint prefixes (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | x :: xs => [x] :: (map (cons x) (prefixes xs))
  end.

Fixpoint subarrays (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | x :: xs => (prefixes (x :: xs)) ++ (subarrays xs)
  end.

Fixpoint minimum_helper (l : list Z) (current_min : Z) : Z :=
  match l with
  | [] => current_min
  | x :: xs => minimum_helper xs (min x current_min)
  end.

Definition minimum (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => minimum_helper xs x
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  minimum (map sum (subarrays nums)).

Example test_minSubArraySum:
  minSubArraySum [1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -100%Z; -1%Z; 1%Z; -50%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z] = -150%Z.
Proof.
  reflexivity.
Qed.