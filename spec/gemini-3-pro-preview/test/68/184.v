Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let fix aux l even_cnt odd_cnt :=
    match l with
    | [] => [even_cnt; odd_cnt]
    | h :: t =>
      if h >? 5 then [even_cnt; odd_cnt]
      else if Z.even h then aux t (even_cnt + 1) odd_cnt
      else aux t even_cnt (odd_cnt + 1)
    end
  in aux l 0 0.

Example test_case : even_odd_count [2; 4; 7; 6; 8; 2; 3; 2] = [2; 0].
Proof. reflexivity. Qed.