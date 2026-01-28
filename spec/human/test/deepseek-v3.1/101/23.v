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

Definition str_The : string := String "T" (String "h" (String "e" "")).
Definition str_quickbrowny : string := String "q" (String "u" (String "i" (String "c" (String "k" (String "b" (String "r" (String "o" (String "w" (String "n" (String "y" "")))))))))).
Definition str_f : string := String "f" "".
Definition str_the : string := String "t" (String "h" (String "e" "")).
Definition str_lazy : string := String "l" (String "a" (String "z" (String "y" ""))).
Definition str_dog : string := String "d" (String "o" (String "g" "")).

Example test_words_string:
  words_string (String "T" (String "h" (String "e" (String " " (String "q" (String "u" (String "i" (String "c" (String "k" (String "b" (String "r" (String "o" (String "w" (String "n" (String "y" (String " " (String "f" (String " " (String "t" (String "h" (String "e" (String " " (String "l" (String "a" (String "z" (String "y" (String " " (String "d" (String "o" (String "g" "")))))))))))))))))))))))))))))) =
  [str_The; str_quickbrowny; str_f; str_the; str_lazy; str_dog].
Proof.
  unfold words_string, words_string_list_impl.
  compute.
  reflexivity.
Qed.