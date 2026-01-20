Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint count_occ (l : list Z) (x : Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eq_dec h x then 1 else 0) + count_occ t x
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => Z.leb x (count_occ l x)) l in
  fold_left Z.max candidates (-1).

Example search_example : search [2%Z; 3%Z; 3%Z; 2%Z; 2%Z] = 2%Z.
Proof. compute. reflexivity. Qed.