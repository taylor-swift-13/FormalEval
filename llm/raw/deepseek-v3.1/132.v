
Definition is_nested_spec (string : list ascii) (result : bool) : Prop :=
  result = true <-> exists i, i < length string /\ nth i string = "["%char /\
    exists max_nest, max_nest >= 2 /\
    exists cnt j, j >= i /\ j < length string /\
      (forall k, i <= k <= j -> 
        (nth k string = "["%char -> cnt (k+1) = cnt k + 1) /\
        (nth k string = "]"%char -> cnt (k+1) = cnt k - 1)) /\
      cnt i = 0 /\ cnt (j+1) = 0 /\
      (forall k, i <= k <= j -> max_nest >= cnt k).
