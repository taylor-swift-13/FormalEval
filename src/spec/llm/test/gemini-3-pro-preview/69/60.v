Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition count (val : Z) (l : list Z) : Z :=
  fold_right (fun x acc => if Z.eqb x val then 1 + acc else acc) 0 l.

Definition search (l : list Z) : Z :=
  let p x := Z.eqb (count x l) x in
  let filtered := filter p l in
  fold_right Z.max (-1) filtered.

Example test_case : search [9%Z; 6%Z; 4%Z; 10%Z; 5%Z; 3%Z; 5%Z; 3%Z; 5%Z; 5%Z] = -1%Z.
Proof.
  compute.
  reflexivity.
Qed.