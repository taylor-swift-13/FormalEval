Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (l : list Z) (x : Z) : Z :=
  match l with
  | [] => 0
  | h :: t => if Z.eqb h x then 1 + count t x else count t x
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => Z.geb (count l x) x) l in
  fold_left Z.max candidates (-1).

Example test_search: search [1%Z; 2%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z] = 4%Z.
Proof. reflexivity. Qed.