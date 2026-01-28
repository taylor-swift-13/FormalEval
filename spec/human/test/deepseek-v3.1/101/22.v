Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition is_delimiter (c : ascii) : bool :=
  match c with
  | ","%char | " "%char => true | _ => false end.

Fixpoint words_string_aux (current_word : list ascii) (input : list ascii) : list (list ascii) :=
  match input with
  | [] => match current_word with [] => [] | _ => [current_word] end
  | c :: cs => if is_delimiter c then
                 match current_word with
                 | [] => words_string_aux [] cs
                 | _ => current_word :: words_string_aux [] cs
                 end
               else words_string_aux (current_word ++ [c]) cs
  end.

Definition words_string_list_impl (s : list ascii) : list (list ascii) :=
  words_string_aux [] s.

Definition words_string (s : string) : list string :=
  map string_of_list_ascii (words_string_list_impl (list_ascii_of_string s)).

(* Define the string literals using String.append *)
Definition str_Hi : string := String "H" (String "i" "").
Definition str_my : string := String "m" (String "y" "").
Definition str_name : string := String "n" (String "a" (String "m" (String "e" ""))).
Definition str_is : string := String "i" (String "s" "").
Definition str_John : string := String "J" (String "o" (String "h" (String "n" ""))).

Lemma test_words_string:
  words_string (String " " (String " " (String " " ""))) = [].
Proof.
  unfold words_string, words_string_list_impl.
  (* The input list of ascii is three spaces *)
  simpl.
  (* The auxiliary function should handle continuous delimiters *)
  simpl.
  reflexivity.
Qed.