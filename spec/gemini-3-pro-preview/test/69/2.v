Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occ (n : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eq_dec h n then 1 else 0) + count_occ n t
  end.

Definition search (l : list Z) : Z :=
  let filtered := filter (fun x => x <=? count_occ x l) l in
  fold_left Z.max filtered (-1).

Example test_search: search [4%Z; 1%Z; 4%Z; 1%Z; 4%Z; 4%Z] = 4%Z.
Proof.
  reflexivity.
Qed.