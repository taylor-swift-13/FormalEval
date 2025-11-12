
Require Import List ZArith.
Import ListNotations.

Definition solution_spec (lst : list Z) (result : Z) : Prop :=
  result = sum_Z (map (fun '(i, x) => x) 
                   (filter (fun '(i, x) => i mod 2 =? 0 /\ x mod 2 =? 1) 
                           (seq 0 (length lst) combine lst))).
