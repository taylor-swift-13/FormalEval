Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition count (l : list Z) (x : Z) : Z :=
  Z.of_nat (length (filter (fun n => n =? x) l)).

Definition search (l : list Z) : Z :=
  let valid := filter (fun x => count l x >=? x) l in
  fold_right Z.max (-1) valid.

Example test_search : search [1; 2; 3; 4; 5; 6; 7; 8; 10; 10; 10; 10; 10; 10; 11; 12; 13; 14; 15] = 1.
Proof.
  reflexivity.
Qed.