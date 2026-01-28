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

Fixpoint subarrays (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | h :: t => prefixes (h :: t) ++ subarrays t
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match map sum (subarrays nums) with
  | [] => 0
  | h :: t => fold_left Z.min t h
  end.

Example test_minSubArraySum: minSubArraySum [3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 0%Z; 9%Z; -10%Z; -10%Z] = -20%Z.
Proof. reflexivity. Qed.