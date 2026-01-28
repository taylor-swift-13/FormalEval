Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint find_min_idx_aux (l : list Z) (cur_min : Z) (min_idx : Z) (cur_idx : Z) : (Z * Z) :=
  match l with
  | [] => (cur_min, min_idx)
  | x :: xs =>
      if x <? cur_min then
        find_min_idx_aux xs x cur_idx (cur_idx + 1)
      else
        find_min_idx_aux xs cur_min min_idx (cur_idx + 1)
  end.

Definition program (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
      let (m, i) := find_min_idx_aux xs x 0 1 in
      [m; i]
  end.

Example test_case_1: program [0%Z; 7%Z; 2%Z; 10%Z; 3%Z; 4%Z; 6%Z; 8%Z; 10%Z] = [0%Z; 0%Z].
Proof.
  reflexivity.
Qed.