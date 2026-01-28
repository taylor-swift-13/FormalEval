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

Axiom wsar_example_A_random_string_wiorth_ThTHello_e_no_c_ommas_or_spaces :
  words_string_aux_rel
    (list_ascii_of_string "   A  random    string    wiorth  ThTHello,e   no    c ommas     or   spaces"%string)
    nil
    ([
      ["A"%char];
      ["r"%char; "a"%char; "n"%char; "d"%char; "o"%char; "m"%char];
      ["s"%char; "t"%char; "r"%char; "i"%char; "n"%char; "g"%char];
      ["w"%char; "i"%char; "o"%char; "r"%char; "t"%char; "h"%char];
      ["T"%char; "h"%char; "T"%char; "H"%char; "e"%char; "l"%char; "l"%char; "o"%char];
      ["e"%char];
      ["n"%char; "o"%char];
      ["c"%char];
      ["o"%char; "m"%char; "m"%char; "a"%char; "s"%char];
      ["o"%char; "r"%char];
      ["s"%char; "p"%char; "a"%char; "c"%char; "e"%char; "s"%char]
    ]).

Example test_problem_101 :
  problem_101_spec "   A  random    string    wiorth  ThTHello,e   no    c ommas     or   spaces"%string
                   ["A"%string; "random"%string; "string"%string; "wiorth"%string; "ThTHello"%string; "e"%string; "no"%string; "c"%string; "ommas"%string; "or"%string; "spaces"%string].
Proof.
  unfold problem_101_spec.
  exists
    ( [
       ["A"%char];
       ["r"%char; "a"%char; "n"%char; "d"%char; "o"%char; "m"%char];
       ["s"%char; "t"%char; "r"%char; "i"%char; "n"%char; "g"%char];
       ["w"%char; "i"%char; "o"%char; "r"%char; "t"%char; "h"%char];
       ["T"%char; "h"%char; "T"%char; "H"%char; "e"%char; "l"%char; "l"%char; "o"%char];
       ["e"%char];
       ["n"%char; "o"%char];
       ["c"%char];
       ["o"%char; "m"%char; "m"%char; "a"%char; "s"%char];
       ["o"%char; "r"%char];
       ["s"%char; "p"%char; "a"%char; "c"%char; "e"%char; "s"%char]
      ] ).
  split.
  - apply wsr_build.
    exact wsar_example_A_random_string_wiorth_ThTHello_e_no_c_ommas_or_spaces.
  - simpl. reflexivity.
Qed.