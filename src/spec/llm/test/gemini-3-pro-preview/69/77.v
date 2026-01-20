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
  fold_left (fun acc x => if Z.leb x (count x l) then Z.max acc x else acc) l (-1).

Example test_search : search [4%Z; 5%Z; 4%Z; 3%Z; 1%Z; 4%Z] = 1%Z.
Proof. reflexivity. Qed.