Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occ (n : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eq_dec h n then 1 else 0) + count_occ n t
  end.

Definition search (l : list Z) : Z :=
  let valid x := count_occ x l >=? x in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_search : search [5; 5; 6; 4; 5; 3; 5; 5] = 5.
Proof. reflexivity. Qed.