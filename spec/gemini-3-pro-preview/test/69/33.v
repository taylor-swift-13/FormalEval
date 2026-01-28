Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition count (l : list Z) (x : Z) : Z :=
  fold_right (fun y c => if Z.eq_dec y x then c + 1 else c) 0 l.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => x <=? count l x) l in
  fold_right Z.max (-1) candidates.

Example test_search: search [2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z] = 2%Z.
Proof.
  reflexivity.
Qed.