Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occ_Z (l : list Z) (x : Z) : Z :=
  Z.of_nat (count_occ Z.eq_dec l x).

Definition search (lst : list Z) : Z :=
  let candidates := filter (fun x => count_occ_Z lst x >=? x) lst in
  fold_right Z.max (-1) candidates.

Example test_case: search [1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z] = 4%Z.
Proof. reflexivity. Qed.