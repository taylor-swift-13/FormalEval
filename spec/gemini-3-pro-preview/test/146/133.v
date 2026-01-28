Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pairs_sum_to_zero_aux (l : list Z) : bool :=
  match l with
  | [] => false
  | x :: xs => existsb (fun y => Z.eqb (x + y) 0) xs || pairs_sum_to_zero_aux xs
  end.

Definition pairs_sum_to_zero (l : list Z) : Z :=
  if pairs_sum_to_zero_aux l then 0 else 1.

Example test_pairs_sum_to_zero: pairs_sum_to_zero [-122; 456; 789; 456] = 1.
Proof. reflexivity. Qed.