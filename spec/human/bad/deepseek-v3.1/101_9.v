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

Definition str_Elephant : string := String "E" (String "l" (String "e" (String "p" (String "h" (String "a" (String "n" (String "t" ""))))))).
Definition str_giraffe : string := String "g" (String "i" (String "r" (String "a" (String "f" (String "f" (String "e" "")))))).
Definition str_lion : string := String "l" (String "i" (String "o" (String "n" ""))).
Definition str_zebra : string := String "z" (String "e" (String "b" (String "r" (String "a" "")))).

Lemma test_words_string:
  words_string (String "E" (String "l" (String "e" (String "p" (String "h" (String "a" (String "n" (String "t" (String "," (String "g" (String "i" (String "r" (String "a" (String "f" (String "f" (String "e" (String "," (String "," (String "l" (String "i" (String "o" (String "n" (String "," (String "z" (String "e" (String "b" (String "r" (String "a" ""))))))))))))))))))))))))))) =
  [str_Elephant; str_giraffe; str_lion; str_zebra].
Proof.
  unfold words_string, words_string_list_impl.
  compute.
  reflexivity.
Qed.
Qed.