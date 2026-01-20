Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint sum_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => h + sum_list t
  end.

Fixpoint prefixes (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | h :: t => [h] :: map (cons h) (prefixes t)
  end.

Fixpoint all_subarrays (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | h :: t => prefixes (h :: t) ++ all_subarrays t
  end.

Fixpoint min_list_aux (acc : Z) (l : list Z) : Z :=
  match l with
  | [] => acc
  | h :: t => min_list_aux (Z.min acc h) t
  end.

Definition min_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => min_list_aux h t
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  min_list (map sum_list (all_subarrays nums)).

Example test_minSubArraySum: minSubArraySum [-20; 30; 50; 70; -80; 90; -100] = -100.
Proof. reflexivity. Qed.