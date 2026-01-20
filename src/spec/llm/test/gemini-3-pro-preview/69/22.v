Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (n : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if h =? n then 1 else 0) + count n t
  end.

Definition search (l : list Z) : Z :=
  let valid n := n <=? count n l in
  fold_right Z.max (-1) (filter valid l).

Example test_search : search [9; 7; 7; 2; 4; 7; 2; 10; 9; 7; 5; 7; 2] = 2.
Proof. reflexivity. Qed.