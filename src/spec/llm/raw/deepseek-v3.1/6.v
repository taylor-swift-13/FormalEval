
Require Import List ZArith String Ascii.
Import ListNotations.

Definition count_depth_spec (s : string) (depth : Z) : Prop :=
  exists max_depth cnt : Z,
    max_depth = 0 /\
    cnt = 0 /\
    (forall (ch : ascii) (idx : nat),
     nth_error (list_ascii_of_string s) idx = Some ch ->
     (if ascii_dec ch "(" then cnt = cnt + 1
      else if ascii_dec ch ")" then cnt = cnt - 1
      else cnt = cnt) /\
     max_depth = Z.max max_depth cnt) /\
    depth = max_depth.

Definition parse_nested_parens_spec (paren_string : string) (result : list Z) : Prop :=
  exists groups : list string,
    groups = map string_of_list_ascii (split " " (list_ascii_of_string paren_string)) /\
    filter (fun s => s <> "") groups = map (fun s => s) groups /\
    result = map (fun s => proj1_sig (exist _ _ (count_depth_spec s))) groups.
