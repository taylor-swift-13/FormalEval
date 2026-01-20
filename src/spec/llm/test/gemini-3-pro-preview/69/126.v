Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (v : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if Z.eqb v x then 1 else 0) + count v xs
  end.

Definition search (l : list Z) : Z :=
  let filtered := filter (fun x => count x l >=? x) l in
  fold_right Z.max (-1) filtered.

Example test_search: search [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20] = 1.
Proof. reflexivity. Qed.