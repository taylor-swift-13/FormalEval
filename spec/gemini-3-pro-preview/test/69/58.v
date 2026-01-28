Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := fold_right (fun y c => if Z.eqb x y then c + 1 else c) 0 l in
  let p (x : Z) := (0 <? x) && (x <=? count x) in
  let valid := filter p l in
  fold_right Z.max (-1) valid.

Example test_search: search [10%Z; 5%Z; 4%Z; 3%Z; 5%Z; 8%Z] = (-1)%Z.
Proof.
  compute. reflexivity.
Qed.