
Require Import List Arith.
Import ListNotations.

Definition sort_third_spec (l l' : list nat) : Prop :=
  length l' = length l /\
  (forall i, i < length l -> 
    (Nat.modulo i 3 = 0 -> nth i l' 0 = nth (Nat.div i 3) (sort le (filter (fun j => Nat.modulo j 3 = 0) (seq 0 (length l)) l)) 0) /\
    (Nat.modulo i 3 <> 0 -> nth i l' 0 = nth i l 0))).
