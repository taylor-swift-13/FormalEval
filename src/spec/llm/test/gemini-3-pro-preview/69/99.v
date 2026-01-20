Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb x h then 1 else 0) + count x t
  end.

Definition search (l : list Z) : Z :=
  fold_right Z.max (-1) (map (fun x => if x <=? count x l then x else -1) l).

Example test_search: search [2%Z; 2%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z] = 4%Z.
Proof.
  reflexivity.
Qed.