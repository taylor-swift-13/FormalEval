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

Axiom wsar_example_Amazing_how_a_sentence_can_change_meaning_just_by_adding_or_removing_commas_excl :
  words_string_aux_rel
    (list_ascii_of_string "Amazing, how a sentence can change, meaning just by, adding or removing, commas!"%string)
    nil
    ([
      ["A"%char; "m"%char; "a"%char; "z"%char; "i"%char; "n"%char; "g"%char];
      ["h"%char; "o"%char; "w"%char];
      ["a"%char];
      ["s"%char; "e"%char; "n"%char; "t"%char; "e"%char; "n"%char; "c"%char; "e"%char];
      ["c"%char; "a"%char; "n"%char];
      ["c"%char; "h"%char; "a"%char; "n"%char; "g"%char; "e"%char];
      ["m"%char; "e"%char; "a"%char; "n"%char; "i"%char; "n"%char; "g"%char];
      ["j"%char; "u"%char; "s"%char; "t"%char];
      ["b"%char; "y"%char];
      ["a"%char; "d"%char; "d"%char; "i"%char; "n"%char; "g"%char];
      ["o"%char; "r"%char];
      ["r"%char; "e"%char; "m"%char; "o"%char; "v"%char; "i"%char; "n"%char; "g"%char];
      ["c"%char; "o"%char; "m"%char; "m"%char; "a"%char; "s"%char; "!"%char]
    ]).

Example test_problem_101 :
  problem_101_spec "Amazing, how a sentence can change, meaning just by, adding or removing, commas!"%string
                   ["Amazing"%string; "how"%string; "a"%string; "sentence"%string; "can"%string; "change"%string; "meaning"%string; "just"%string; "by"%string; "adding"%string; "or"%string; "removing"%string; "commas!"%string].
Proof.
  unfold problem_101_spec.
  exists
    ( [
       ["A"%char; "m"%char; "a"%char; "z"%char; "i"%char; "n"%char; "g"%char];
       ["h"%char; "o"%char; "w"%char];
       ["a"%char];
       ["s"%char; "e"%char; "n"%char; "t"%char; "e"%char; "n"%char; "c"%char; "e"%char];
       ["c"%char; "a"%char; "n"%char];
       ["c"%char; "h"%char; "a"%char; "n"%char; "g"%char; "e"%char];
       ["m"%char; "e"%char; "a"%char; "n"%char; "i"%char; "n"%char; "g"%char];
       ["j"%char; "u"%char; "s"%char; "t"%char];
       ["b"%char; "y"%char];
       ["a"%char; "d"%char; "d"%char; "i"%char; "n"%char; "g"%char];
       ["o"%char; "r"%char];
       ["r"%char; "e"%char; "m"%char; "o"%char; "v"%char; "i"%char; "n"%char; "g"%char];
       ["c"%char; "o"%char; "m"%char; "m"%char; "a"%char; "s"%char; "!"%char]
      ] ).
  split.
  - apply wsr_build.
    exact wsar_example_Amazing_how_a_sentence_can_change_meaning_just_by_adding_or_removing_commas_excl.
  - simpl. reflexivity.
Qed.