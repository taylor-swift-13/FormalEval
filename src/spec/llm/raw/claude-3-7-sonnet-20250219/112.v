
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Definition is_palindrome (s : string) : bool :=
  let fix rev_aux (l1 l2 : list ascii) : bool :=
      match l1, l2 with
      | [], [] => true
      | x :: xs, y :: ys => if ascii_dec x y then rev_aux xs ys else false
      | _, _ => false
      end
  in
  let l := list_ascii_of_string s in
  rev_aux l (rev l).

Definition filter_not_in (s c : string) : string :=
  let fix aux (l : list ascii) : list ascii :=
      match l with
      | [] => []
      | x :: xs => if existsb (fun ch => if ascii_dec x ch then true else false) (list_ascii_of_string c)
                   then aux xs
                   else x :: aux xs
      end
  in
  string_of_list_ascii (aux (list_ascii_of_string s)).

Definition reverse_delete_spec (s c r : string) (b : bool) : Prop :=
  r = filter_not_in s c /\
  b = is_palindrome r.
