Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count x := fold_right (fun y c => if Z.eq_dec x y then c + 1 else c) 0 l in
  fold_right Z.max (-1) (filter (fun x => x <=? count x) l).

Example test_case : search [1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 2%Z] = 2%Z.
Proof.
  compute. reflexivity.
Qed.