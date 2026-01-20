
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition strange_sort_list_spec (lst sorted_ans : list nat) : Prop :=
  let sorted_list := sort Nat.leb lst in
  exists i j ans,
    i = 0 /\
    j = length sorted_list - 1 /\
    sorted_ans = ans /\
    (* ans is constructed by alternately taking from sorted_list[i] and sorted_list[j] until i >= j *)
    (
      (* For the indices handled by pairs *)
      (forall k, k < (j - i + 1) / 2 ->
        nth (2 * k) ans 0 = nth (i + k) sorted_list 0 /\
        nth (2 * k + 1) ans 0 = nth (j - k) sorted_list 0
      ) /\
      (* If odd number of elements, last element in ans is the middle element *)
      ( (i = j -> nth (length ans - 1) ans 0 = nth i sorted_list 0) \/
        (i <> j -> length ans = 2 * ((j - i + 1) / 2))
      )
    ).
