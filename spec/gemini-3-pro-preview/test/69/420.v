Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (l : list Z) (x : Z) : Z :=
  fold_right (fun y c => if Z.eqb y x then c + 1 else c) 0 l.

Definition search (l : list Z) : Z :=
  let filtered := filter (fun x => Z.eqb (count l x) x) l in
  fold_right Z.max (-1) filtered.

Example test_case: search [5%Z; 1%Z; 2%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z] = 3%Z.
Proof.
  compute. reflexivity.
Qed.