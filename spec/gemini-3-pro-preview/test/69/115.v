Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occ (z : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if Z.eq_dec x z then 1 else 0) + count_occ z xs
  end.

Definition search (l : list Z) : Z :=
  let filtered := filter (fun x => x <=? count_occ x l) l in
  fold_right Z.max (-1) filtered.

Example test_search: search [4; 5; 6; 4; 5; 3; 5; 5; 4] = -1.
Proof.
  reflexivity.
Qed.