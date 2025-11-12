
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Sets.Ensembles.

Definition same_chars_spec (s0 s1 : string) (result : bool) : Prop :=
  result = if string_dec (list_to_set (string_to_list s0)) (list_to_set (string_to_list s1)) then true else false.

(* Auxiliary functions *)
Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => nil
  | String c s' => c :: string_to_list s'
  end.

Fixpoint list_to_set (l : list ascii) : Ensemble ascii :=
  match l with
  | nil => Empty_set ascii
  | cons x xs => Add ascii (list_to_set xs) x
  end.
