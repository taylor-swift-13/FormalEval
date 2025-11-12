
Require Import List Ascii String.
Import ListNotations.

Definition digitSum_spec (s : string) (sum : nat) : Prop :=
  sum = fold_left plus (map (fun ch => nat_of_ascii ch) 
                         (filter (fun ch => is_upper ch) (list_ascii_of_string s))) 0.
