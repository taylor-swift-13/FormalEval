Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_elements (l : list Z) : Z :=
  let s := fold_right Z.add 0 (filter (fun x => x <? 0) l) in
  if s =? 0 then 1 else s.

Example test_add_elements : add_elements [3%Z; -8%Z; -9%Z; -9%Z; -7%Z; -5%Z; -60%Z; -9%Z; -2%Z; -1%Z; -5%Z; -8%Z] = -123%Z.
Proof. reflexivity. Qed.