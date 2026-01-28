Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let valid := filter (fun x => x <=? Z.of_nat (count_occ Z.eq_dec l x)) l in
  match valid with
  | [] => -1
  | x :: xs => fold_right Z.max x xs
  end.

Example test_search: search [1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 17; 3; 3; 19; 3; 4; 4; 4; 4; 4; 4] = 4.
Proof. reflexivity. Qed.