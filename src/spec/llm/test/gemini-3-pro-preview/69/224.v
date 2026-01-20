Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solve (lst : list Z) : Z :=
  let distinct := nodup Z.eq_dec lst in
  let lucky := filter (fun x => Z.eqb (Z.of_nat (count_occ Z.eq_dec lst x)) x) distinct in
  fold_right Z.max (-1) lucky.

Example test_case: solve [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 4%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 15%Z; 1%Z; 1%Z; 2%Z; 1%Z; 2%Z; 2%Z; 2%Z; 18%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 7%Z; 8%Z; 8%Z; 8%Z; 9%Z; 7%Z; 9%Z; 10%Z; 10%Z; 10%Z] = 4%Z.
Proof.
  reflexivity.
Qed.