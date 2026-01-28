Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint prefixes (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => x :: map (Z.add x) (prefixes xs)
  end.

Fixpoint all_sums (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => prefixes (x :: xs) ++ all_sums xs
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match all_sums nums with
  | [] => 0
  | y :: ys => fold_left Z.min ys y
  end.

Example test_minSubArraySum: minSubArraySum [5%Z; -1%Z; -2%Z; -2%Z; -4%Z; 6%Z; -1%Z; -1%Z] = -9%Z.
Proof. reflexivity. Qed.