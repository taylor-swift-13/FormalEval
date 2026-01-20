Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (n : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if Z.eqb n x then 1 else 0) + count n xs
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => count x l >=? x) l in
  fold_left Z.max candidates (-1).

Example test_search : search [10; 2; 4; 4; 4; 4; 4; 4; 5; 2] = 4.
Proof. reflexivity. Qed.