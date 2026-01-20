
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition double_the_difference_spec (lst : list Z) (ans : Z) : Prop :=
  ans = fold_right (fun num acc => 
    if (num >? 0) && (Z.odd num) then acc + num * num else acc
  ) 0 lst.
