
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Definition check_dict_case_spec (dict : list (string * string)) (result : bool) : Prop :=
  let keys := map fst dict in
  if keys is nil then
    result = false
  else
    (forall k, In k keys -> exists s : string, k = s) /\
    (result = true <-> 
      (forall k, In k keys -> (exists s : string, k = s /\ forall c, In c (list_ascii_of_string s) -> is_lower c)) \/
      (forall k, In k keys -> (exists s : string, k = s /\ forall c, In c (list_ascii_of_string s) -> is_upper c))).
