Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (l : list Z) (x : Z) : Z :=
  fold_right (fun y acc => if Z.eq_dec y x then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => count l x >=? x) l in
  fold_right Z.max (-1) candidates.

Example test_search: search [2%Z; 2%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 3%Z; 6%Z; 4%Z; 5%Z; 5%Z; 5%Z; 3%Z] = 4%Z.
Proof.
  compute.
  reflexivity.
Qed.