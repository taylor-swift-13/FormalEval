Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (n : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb n h then 1 else 0) + count n t
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => x <=? count x l) l in
  fold_left Z.max candidates (-1).

Example search_example: search [5; 5; 6; 4; 5; 3; 5; 5; 5] = 5.
Proof. reflexivity. Qed.