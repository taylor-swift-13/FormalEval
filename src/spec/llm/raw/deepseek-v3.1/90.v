
Require Import List ZArith.
Require Import Coq.Sorting.Sorted.

Definition next_smallest_spec (lst : list Z) (result : option Z) : Prop :=
  match lst with
  | nil => result = None
  | _ :: nil => result = None
  | _ =>
      exists sorted_lst,
        StronglySorted Z.le sorted_lst /\
        Permutation lst sorted_lst /\
        (exists second_smallest,
           result = Some second_smallest /\
           In second_smallest sorted_lst /\
           (forall x, In x sorted_lst -> second_smallest <= x) /\
           (exists count : nat,
              count_occ Z.eq_dec sorted_lst (hd 0 sorted_lst) = 1%nat /\
              second_smallest = nth 1 sorted_lst 0))
  end.
