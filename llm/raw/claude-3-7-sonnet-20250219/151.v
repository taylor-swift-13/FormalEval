
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_integer (n : Z) : Prop := True.

Definition double_the_difference_spec (lst : list Z) (result : Z) : Prop :=
  result = fold_left
    (fun acc num =>
       if (Z.odd num) && (0 <? num) then acc + num * num else acc)
    lst 0.
