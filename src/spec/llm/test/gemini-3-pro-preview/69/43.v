Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition count (l : list Z) (x : Z) : Z :=
  fold_right (fun y c => if Z.eqb y x then c + 1 else c) 0 l.

Definition search (l : list Z) : Z :=
  let p x := andb (0 <? x) (x <=? count l x) in
  let candidates := filter p l in
  fold_right Z.max (-1) candidates.

Example test_search: search [6; 4; 5; 6; 3; 5; 3; 5; 5; 5] = 5.
Proof.
  reflexivity.
Qed.