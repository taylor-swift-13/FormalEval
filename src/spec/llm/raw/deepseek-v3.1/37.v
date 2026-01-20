
Require Import List ZArith.
Import ListNotations.

Definition sort_even_spec (l l' : list Z) : Prop :=
  length l' = length l /\
  (forall i, 0 <= i < length l ->
    (if Z.even i then nth i l' 0 = nth (Z.div (Z.of_nat (count_even_positions i)) 2) (sort (extract_evens l)) 0
     else nth i l' 0 = nth i l 0)) /\
  is_sorted_evens (extract_evens l) (extract_evens l').
