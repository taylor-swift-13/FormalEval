
Require Import List ZArith.
Import ListNotations.

Definition generate_integers_spec (a b : Z) (result : list Z) : Prop :=
  (a > 0) /\ (b > 0) /\
  result = filter (fun i => Z.even i) 
                 (seqZ (Z.min a b) (Z.min (Z.abs (Z.sub (Z.max a b) (Z.min a b) + 1)) 
                                        (Z.sub 10 (Z.min a b)))).
