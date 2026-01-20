
Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  (forall n, In n result -> count_occ Z.eq_dec numbers n = 1) /\
  (forall n, count_occ Z.eq_dec numbers n = 1 -> In n result) /\
  (exists f : nat -> nat, 
     (forall i j, i < j < length result -> f i < f j) /\
     (forall i, i < length result -> nth i result 0 = nth (f i) numbers 0)).
