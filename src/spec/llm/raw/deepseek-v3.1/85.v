
Require Import List ZArith.
Import ListNotations.

Definition add_spec (lst : list Z) (result : Z) : Prop :=
  lst <> [] /\
  result = fold_left (fun acc '(i, x) => if (i mod 2 =? 1) && (x mod 2 =? 0) then acc + x else acc) 
                    (seq 0) (length lst) lst 0.
