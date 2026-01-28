Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint count_occ (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | y :: tl => (if Z.eqb x y then 1 else 0) + count_occ x tl
  end.

Definition search (l : list Z) : Z :=
  let filtered := filter (fun x => x <=? count_occ x l) l in
  fold_right Z.max (-1) filtered.

Example test_case: search [2%Z; 2%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 7%Z; 5%Z; 13%Z; 5%Z] = 2%Z.
Proof. reflexivity. Qed.