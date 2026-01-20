Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint count_occ (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | y :: tl => (if Z.eqb y x then 1 else 0) + count_occ x tl
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => Z.eqb (count_occ x l) x) l in
  fold_right Z.max (-1) candidates.

Example test_search: search [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 2; 2; 3; 3; 4; 4; 4; 5; 5; 5; 6; 6; 6; 7; 7; 7; 8; 8; 8; 9; 8; 9; 10; 10; 10; 5; 1] = 2.
Proof. reflexivity. Qed.