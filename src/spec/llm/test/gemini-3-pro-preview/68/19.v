Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint find_min_aux (l : list Z) (idx : Z) (min_val : Z) (min_idx : Z) : Z * Z :=
  match l with
  | [] => (min_val, min_idx)
  | x :: xs => if x <? min_val
               then find_min_aux xs (idx + 1) x idx
               else find_min_aux xs (idx + 1) min_val min_idx
  end.

Definition solve (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => 
      let (m, i) := find_min_aux xs 1 x 0 in
      [m; i]
  end.

Example test_case: solve [2%Z; 2%Z; 2%Z; 2%Z; 2%Z] = [2%Z; 0%Z].
Proof.
  reflexivity.
Qed.