Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition count (l : list Z) (x : Z) : Z :=
  fold_right (fun y c => if Z.eq_dec y x then c + 1 else c) 0 l.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => x <=? count l x) l in
  fold_right Z.max (-1) candidates.

Example example_test_case: search [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 18%Z; 8%Z; 9%Z; 10%Z; 10%Z; 10%Z; 19%Z; 10%Z; 11%Z; 12%Z; 13%Z; 15%Z; 1%Z; 9%Z] = 1%Z.
Proof.
  compute.
  reflexivity.
Qed.