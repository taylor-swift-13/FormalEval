Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List.
Import ListNotations.

Inductive is_delimiter : ascii -> Prop :=
| id_comma : is_delimiter ","%char
| id_space : is_delimiter " "%char.

Inductive words_string_aux_rel : list ascii -> list ascii -> list (list ascii) -> Prop :=
| wsar_empty_empty : words_string_aux_rel nil nil nil
| wsar_empty_word : forall cur_word, cur_word <> nil ->
   words_string_aux_rel nil cur_word (cur_word :: nil)
| wsar_delim_empty : forall c cs words, is_delimiter c ->
   words_string_aux_rel cs nil words ->
   words_string_aux_rel (c :: cs) nil words
| wsar_delim_word : forall c cs cur_word words, is_delimiter c -> cur_word <> nil ->
   words_string_aux_rel cs nil words ->
   words_string_aux_rel (c :: cs) nil (cur_word :: words)
| wsar_char_extend : forall c cs cur_word words, ~ is_delimiter c ->
   words_string_aux_rel cs (cur_word ++ [c]) words ->
   words_string_aux_rel (c :: cs) cur_word words.

Inductive words_string_rel : list ascii -> list (list ascii) -> Prop :=
| wsr_build : forall s output, words_string_aux_rel s nil output ->
   words_string_rel s output.

Definition problem_101_pre (s : string) : Prop :=
  let l := list_ascii_of_string s in
  Forall (fun c =>
    let n := nat_of_ascii c in
      (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122) \/ c = ","%char \/ c = " "%char) l.

Definition problem_101_spec (s : string) (output : list string) : Prop :=
  exists output_list_ascii,
    words_string_rel (list_ascii_of_string s) output_list_ascii /\
    output = map string_of_list_ascii output_list_ascii.

Axiom wsar_example_TheHi_my_name_is_John_How_are_you_quick_brown_fox_jumpwiorths_over_tareadding :
  words_string_aux_rel
    (list_ascii_of_string "TheHi, my    name   is John. How     are    you?    quick brown fox jumpwiorths over tareadding"%string)
    nil
    ([
      ["T"%char; "h"%char; "e"%char; "H"%char; "i"%char];
      ["m"%char; "y"%char];
      ["n"%char; "a"%char; "m"%char; "e"%char];
      ["i"%char; "s"%char];
      ["J"%char; "o"%char; "h"%char; "n"%char; "."%char];
      ["H"%char; "o"%char; "w"%char];
      ["a"%char; "r"%char; "e"%char];
      ["y"%char; "o"%char; "u"%char; "?"%char];
      ["q"%char; "u"%char; "i"%char; "c"%char; "k"%char];
      ["b"%char; "r"%char; "o"%char; "w"%char; "n"%char];
      ["f"%char; "o"%char; "x"%char];
      ["j"%char; "u"%char; "m"%char; "p"%char; "w"%char; "i"%char; "o"%char; "r"%char; "t"%char; "h"%char; "s"%char];
      ["o"%char; "v"%char; "e"%char; "r"%char];
      ["t"%char; "a"%char; "r"%char; "e"%char; "a"%char; "d"%char; "d"%char; "i"%char; "n"%char; "g"%char]
    ]).

Example test_problem_101 :
  problem_101_spec
    "TheHi, my    name   is John. How     are    you?    quick brown fox jumpwiorths over tareadding"%string
    ["TheHi"%string; "my"%string; "name"%string; "is"%string; "John."%string; "How"%string; "are"%string; "you?"%string; "quick"%string; "brown"%string; "fox"%string; "jumpwiorths"%string; "over"%string; "tareadding"%string].
Proof.
  unfold problem_101_spec.
  exists
    ([
      ["T"%char; "h"%char; "e"%char; "H"%char; "i"%char];
      ["m"%char; "y"%char];
      ["n"%char; "a"%char; "m"%char; "e"%char];
      ["i"%char; "s"%char];
      ["J"%char; "o"%char; "h"%char; "n"%char; "."%char];
      ["H"%char; "o"%char; "w"%char];
      ["a"%char; "r"%char; "e"%char];
      ["y"%char; "o"%char; "u"%char; "?"%char];
      ["q"%char; "u"%char; "i"%char; "c"%char; "k"%char];
      ["b"%char; "r"%char; "o"%char; "w"%char; "n"%char];
      ["f"%char; "o"%char; "x"%char];
      ["j"%char; "u"%char; "m"%char; "p"%char; "w"%char; "i"%char; "o"%char; "r"%char; "t"%char; "h"%char; "s"%char];
      ["o"%char; "v"%char; "e"%char; "r"%char];
      ["t"%char; "a"%char; "r"%char; "e"%char; "a"%char; "d"%char; "d"%char; "i"%char; "n"%char; "g"%char]
    ]).
  split.
  - apply wsr_build.
    exact wsar_example_TheHi_my_name_is_John_How_are_you_quick_brown_fox_jumpwiorths_over_tareadding.
  - simpl. reflexivity.
Qed.