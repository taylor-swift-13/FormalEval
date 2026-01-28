Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb x h then 1 else 0) + count x t
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => x <=? count x l) l in
  fold_right Z.max (-1) candidates.

Example test_search: search [1; 2; 3; 4; 5; 6; 7; 8; 10; 5; 7; 8; 9; 10; 5; 10; 7; 8; 9; 10; 5; 6; 7; 8; 9; 10; 5; 6; 7; 8; 9; 10] = 5.
Proof. reflexivity. Qed.