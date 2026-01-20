Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint prefixes (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | x :: xs => [x] :: map (cons x) (prefixes xs)
  end.

Fixpoint all_sublists (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | x :: xs => prefixes (x :: xs) ++ all_sublists xs
  end.

Fixpoint sum (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => h + sum t
  end.

Fixpoint min_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => Z.min x (min_list xs)
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  min_list (map sum (all_sublists nums)).

Example test_minSubArraySum:
  minSubArraySum [1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 90%Z; 0%Z; 0%Z; 1%Z; -1%Z; 1%Z; -1%Z; -70%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 0%Z; 1%Z; 1%Z; -1%Z; 0%Z] = -72%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.