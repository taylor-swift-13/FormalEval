Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint prefix_sums (acc : Z) (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => (acc + x) :: prefix_sums (acc + x) xs
  end.

Fixpoint all_subarray_sums_aux (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => (prefix_sums 0 l) ++ (all_subarray_sums_aux xs)
  end.

Fixpoint min_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => Z.min x (min_list xs)
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  min_list (all_subarray_sums_aux nums).

Example test_minSubArraySum:
  minSubArraySum [100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; -10%Z; 100000%Z; -3%Z; -50000%Z; 50000%Z; -100000%Z; -50000%Z; -50000%Z] = -200013%Z.
Proof. reflexivity. Qed.