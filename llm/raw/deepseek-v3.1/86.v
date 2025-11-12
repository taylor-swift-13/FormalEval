
Require Import String List Ascii.
Require Import Sorting.Permutation.

Definition anti_shuffle_spec (s : string) (result : string) : Prop :=
  exists words : list string,
    s = concat (map (fun w => w ++ " ") (removelast words)) ++ last words "" /\
    result = concat (map (fun w => w ++ " ") (removelast (map (fun w => string_sort w) words))) ++ last (map (fun w => string_sort w) words) "" /\
    Forall (fun w => exists sorted_w : string, 
                     Permutation (list_ascii_of_string w) (list_ascii_of_string sorted_w) /\
                     sorted_w = string_sort w) words.
