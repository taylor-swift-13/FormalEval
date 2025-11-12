
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Definition check_dict_case_spec (dict : list (string * string)) (result : bool) : Prop :=
  let keys := map fst dict in
  result = false <-> keys = nil \/
  result = true <->
    (forall k, In k keys -> (exists s, k = s /\ forall c, In c (list_of_string s) -> is_lower c) \/
                               (exists s, k = s /\ forall c, In c (list_of_string s) -> is_upper c)) /\
    (exists b, b = true /\ forall k, In k keys -> 
                (exists s, k = s /\ forall c, In c (list_of_string s) -> is_lower c) \/
                (exists s, k = s /\ forall c, In c (list_of_string s) -> is_upper c)).
