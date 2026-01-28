Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eq_dec x h then 1 else 0) + count x t
  end.

Definition solve (l : list Z) : Z :=
  let lucky := filter (fun x => Z.eqb (count x l) x) l in
  fold_right Z.max (-1) lucky.

Example test_case_2:
  solve [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 2; 1; 1; 1; 2; 2; 18; 3; 3; 3; 4; 4; 4; 5; 5; 13; 5; 6; 6; 7; 7; 7; 7; 8; 8; 8; 9; 9; 9; 10; 10; 10; 1] = 3.
Proof.
  reflexivity.
Qed.