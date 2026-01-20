
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition reverse (s : string) : string :=
  let fix rev_aux (l : list ascii) :=
      match l with
      | [] => []
      | x :: xs => rev_aux xs ++ [x]
      end in
  String.of_list (rev_aux (String.to_list s)).

Definition is_palindrome_spec (s : string) (b : bool) : Prop :=
  b = Bool.eqb s (reverse s).

Definition make_palindrome_spec (s p : string) : Prop :=
  is_palindrome_spec s true -> p = s /\
  (forall i, 
    let suffix := substring i (String.length s - i) s in
    is_palindrome_spec suffix true -> 
      p = s ++ (reverse (substring 0 i s))) /\
  is_palindrome_spec p true /\
  (String.length p >= String.length s).

