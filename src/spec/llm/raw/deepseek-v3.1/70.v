
Require Import List ZArith.
Import ListNotations.

Definition strange_sort_list_spec (lst : list Z) (result : list Z) : Prop :=
  exists sorted_lst : list Z,
    StronglySorted Z.le sorted_lst /\
    Permutation lst sorted_lst /\
    (let n := length sorted_lst in
     result = flat_map (fun i => [nth i sorted_lst 0; nth (n - 1 - i) sorted_lst 0])
                      (seq 0 (n / 2)) ++
              (if Nat.even n then [] else [nth (n / 2) sorted_lst 0])).
