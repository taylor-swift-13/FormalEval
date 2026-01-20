
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition is_vowel (ch : ascii) : bool :=
  let c := nat_of_ascii ch in
  match c with
  | 97 => true   (* a *)
  | 101 => true  (* e *)
  | 105 => true  (* i *)
  | 111 => true  (* o *)
  | 117 => true  (* u *)
  | 65 => true   (* A *)
  | 69 => true   (* E *)
  | 73 => true   (* I *)
  | 79 => true   (* O *)
  | 85 => true   (* U *)
  | _ => false
  end.

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: string_to_list rest
  end.

Fixpoint list_to_string (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String c (list_to_string rest)
  end.

Definition remove_vowels_spec (text : string) (result : string) : Prop :=
  result = list_to_string (filter (fun ch => negb (is_vowel ch)) (string_to_list text)).
