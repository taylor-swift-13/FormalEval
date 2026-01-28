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

Axiom wsar_example_dog_commaTheHi_my_name_is_John_How_are_yo_A_random_string_with_no_commas_r_or_spacesu_quick_brown_fox_jumpwiorths_over_tsarelazy_dog_ses :
  words_string_aux_rel
    (list_ascii_of_string "dog.commaTheHi, my    name   is John. How     are    yo   A  random    string    with      no    commas    r or   spacesu?    quick brown fox jumpwiorths over tsarelazy dog.ses"%string)
    nil
    ([
      ["d"%char; "o"%char; "g"%char; "."%char; "c"%char; "o"%char; "m"%char; "m"%char; "a"%char; "T"%char; "h"%char; "e"%char; "H"%char; "i"%char];
      ["m"%char; "y"%char];
      ["n"%char; "a"%char; "m"%char; "e"%char];
      ["i"%char; "s"%char];
      ["J"%char; "o"%char; "h"%char; "n"%char; "."%char];
      ["H"%char; "o"%char; "w"%char];
      ["a"%char; "r"%char; "e"%char];
      ["y"%char; "o"%char];
      ["A"%char];
      ["r"%char; "a"%char; "n"%char; "d"%char; "o"%char; "m"%char];
      ["s"%char; "t"%char; "r"%char; "i"%char; "n"%char; "g"%char];
      ["w"%char; "i"%char; "t"%char; "h"%char];
      ["n"%char; "o"%char];
      ["c"%char; "o"%char; "m"%char; "m"%char; "a"%char; "s"%char];
      ["r"%char];
      ["o"%char; "r"%char];
      ["s"%char; "p"%char; "a"%char; "c"%char; "e"%char; "s"%char; "u"%char; "?"%char];
      ["q"%char; "u"%char; "i"%char; "c"%char; "k"%char];
      ["b"%char; "r"%char; "o"%char; "w"%char; "n"%char];
      ["f"%char; "o"%char; "x"%char];
      ["j"%char; "u"%char; "m"%char; "p"%char; "w"%char; "i"%char; "o"%char; "r"%char; "t"%char; "h"%char; "s"%char];
      ["o"%char; "v"%char; "e"%char; "r"%char];
      ["t"%char; "s"%char; "a"%char; "r"%char; "e"%char; "l"%char; "a"%char; "z"%char; "y"%char];
      ["d"%char; "o"%char; "g"%char; "."%char; "s"%char; "e"%char; "s"%char]
    ]).

Example test_problem_101 :
  problem_101_spec "dog.commaTheHi, my    name   is John. How     are    yo   A  random    string    with      no    commas    r or   spacesu?    quick brown fox jumpwiorths over tsarelazy dog.ses"%string
                   ["dog.commaTheHi"%string; "my"%string; "name"%string; "is"%string; "John."%string; "How"%string; "are"%string; "yo"%string; "A"%string; "random"%string; "string"%string; "with"%string; "no"%string; "commas"%string; "r"%string; "or"%string; "spacesu?"%string; "quick"%string; "brown"%string; "fox"%string; "jumpwiorths"%string; "over"%string; "tsarelazy"%string; "dog.ses"%string].
Proof.
  unfold problem_101_spec.
  exists
    ( [
       ["d"%char; "o"%char; "g"%char; "."%char; "c"%char; "o"%char; "m"%char; "m"%char; "a"%char; "T"%char; "h"%char; "e"%char; "H"%char; "i"%char];
       ["m"%char; "y"%char];
       ["n"%char; "a"%char; "m"%char; "e"%char];
       ["i"%char; "s"%char];
       ["J"%char; "o"%char; "h"%char; "n"%char; "."%char];
       ["H"%char; "o"%char; "w"%char];
       ["a"%char; "r"%char; "e"%char];
       ["y"%char; "o"%char];
       ["A"%char];
       ["r"%char; "a"%char; "n"%char; "d"%char; "o"%char; "m"%char];
       ["s"%char; "t"%char; "r"%char; "i"%char; "n"%char; "g"%char];
       ["w"%char; "i"%char; "t"%char; "h"%char];
       ["n"%char; "o"%char];
       ["c"%char; "o"%char; "m"%char; "m"%char; "a"%char; "s"%char];
       ["r"%char];
       ["o"%char; "r"%char];
       ["s"%char; "p"%char; "a"%char; "c"%char; "e"%char; "s"%char; "u"%char; "?"%char];
       ["q"%char; "u"%char; "i"%char; "c"%char; "k"%char];
       ["b"%char; "r"%char; "o"%char; "w"%char; "n"%char];
       ["f"%char; "o"%char; "x"%char];
       ["j"%char; "u"%char; "m"%char; "p"%char; "w"%char; "i"%char; "o"%char; "r"%char; "t"%char; "h"%char; "s"%char];
       ["o"%char; "v"%char; "e"%char; "r"%char];
       ["t"%char; "s"%char; "a"%char; "r"%char; "e"%char; "l"%char; "a"%char; "z"%char; "y"%char];
       ["d"%char; "o"%char; "g"%char; "."%char; "s"%char; "e"%char; "s"%char]
      ] ).
  split.
  - apply wsr_build.
    exact wsar_example_dog_commaTheHi_my_name_is_John_How_are_yo_A_random_string_with_no_commas_r_or_spacesu_quick_brown_fox_jumpwiorths_over_tsarelazy_dog_ses.
  - simpl. reflexivity.
Qed.