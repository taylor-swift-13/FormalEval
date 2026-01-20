Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint prefixes (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | x :: xs => [x] :: map (cons x) (prefixes xs)
  end.

Fixpoint sub_arrays (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | x :: xs => prefixes (x :: xs) ++ sub_arrays xs
  end.

Definition sum_list (l : list Z) : Z := fold_right Z.add 0 l.

Definition minSubArraySum (nums : list Z) : Z :=
  match map sum_list (sub_arrays nums) with
  | [] => 0
  | x :: xs => fold_right Z.min x xs
  end.

Example test_minSubArraySum: minSubArraySum [-10%Z; -30%Z; -50%Z; 60%Z; -70%Z; -7%Z; -90%Z; 100%Z; 100%Z] = -197%Z.
Proof. reflexivity. Qed.