Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let fix count_occ (l : list Z) (x : Z) : Z :=
    match l with
    | [] => 0
    | h :: t => (if Z.eq_dec h x then 1 else 0) + count_occ t x
    end
  in
  let valid := filter (fun x => x <=? count_occ l x) l in
  fold_right Z.max (-1) valid.

Example test_search: search [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 5%Z; 6%Z; 7%Z; 8%Z; 10%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z] = 5%Z.
Proof. reflexivity. Qed.