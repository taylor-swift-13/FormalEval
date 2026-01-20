Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint count (val : Z) (lst : list Z) : Z :=
  match lst with
  | [] => 0
  | h :: t => (if Z.eqb val h then 1 else 0) + count val t
  end.

Definition search (lst : list Z) : Z :=
  let p x := Z.leb x (count x lst) in
  let valid := filter p lst in
  fold_right Z.max (-1) valid.

Example test_search: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 11%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 2%Z; 6%Z; 6%Z; 12%Z; 7%Z; 7%Z; 8%Z; 8%Z; 9%Z; 9%Z; 10%Z; 10%Z; 11%Z; 11%Z; 13%Z; 6%Z] = 4%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.