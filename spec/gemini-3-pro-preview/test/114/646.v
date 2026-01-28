Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint sum (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => h + sum t
  end.

Fixpoint tails {A} (l : list A) : list (list A) :=
  match l with
  | [] => []
  | h :: t => (h :: t) :: tails t
  end.

Fixpoint prefixes {A} (l : list A) : list (list A) :=
  match l with
  | [] => []
  | h :: t => [h] :: map (cons h) (prefixes t)
  end.

Definition all_subarrays (l : list Z) : list (list Z) :=
  flat_map prefixes (tails l).

Definition min_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => fold_left Z.min t h
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  min_list (map sum (all_subarrays nums)).

Example test_minSubArraySum_2 :
  minSubArraySum [1; -1; 1; -1; 1; -1; 1; 1; -1; 1; -1; 1; -1; 90; 0; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; 0; 1] = -1.
Proof. reflexivity. Qed.