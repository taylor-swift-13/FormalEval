Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if x =? h then 1 else 0) + count x t
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => count x l >=? x) l in
  fold_left Z.max candidates (-1).

Example test_search : search [6%Z; 4%Z; 4%Z; 4%Z; 3%Z] = (-1)%Z.
Proof.
  compute.
  reflexivity.
Qed.