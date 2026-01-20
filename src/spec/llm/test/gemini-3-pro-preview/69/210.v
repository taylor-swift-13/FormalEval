Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (val : Z) (lst : list Z) : Z :=
  match lst with
  | [] => 0
  | h :: t => (if Z.eq_dec h val then 1 else 0) + count val t
  end.

Definition search (lst : list Z) : Z :=
  let candidates := filter (fun x => Z.leb x (count x lst)) lst in
  fold_left Z.max candidates (-1).

Example test_search : search [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 18%Z; 8%Z; 9%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 11%Z; 12%Z; 13%Z; 15%Z; 1%Z] = 1%Z.
Proof.
  compute.
  reflexivity.
Qed.