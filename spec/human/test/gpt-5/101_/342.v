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

Axiom wsar_example_tTwo_spaces_after__one_space_before___and_no_spaces_in_betweenh :
  words_string_aux_rel
    (list_ascii_of_string "tTwo spaces after,  one space before  , and no spaces in betweenh"%string)
    nil
    ([
      ["t"%char; "T"%char; "w"%char; "o"%char];
      ["s"%char; "p"%char; "a"%char; "c"%char; "e"%char; "s"%char];
      ["a"%char; "f"%char; "t"%char; "e"%char; "r"%char];
      ["o"%char; "n"%char; "e"%char];
      ["s"%char; "p"%char; "a"%char; "c"%char; "e"%char];
      ["b"%char; "e"%char; "f"%char; "o"%char; "r"%char; "e"%char];
      ["a"%char; "n"%char; "d"%char];
      ["n"%char; "o"%char];
      ["s"%char; "p"%char; "a"%char; "c"%char; "e"%char; "s"%char];
      ["i"%char; "n"%char];
      ["b"%char; "e"%char; "t"%char; "w"%char; "e"%char; "e"%char; "n"%char; "h"%char]
    ]).

Example test_problem_101 :
  problem_101_spec "tTwo spaces after,  one space before  , and no spaces in betweenh"%string
                   ["tTwo"%string; "spaces"%string; "after"%string; "one"%string; "space"%string; "before"%string; "and"%string; "no"%string; "spaces"%string; "in"%string; "betweenh"%string].
Proof.
  unfold problem_101_spec.
  exists
    ( [
       ["t"%char; "T"%char; "w"%char; "o"%char];
       ["s"%char; "p"%char; "a"%char; "c"%char; "e"%char; "s"%char];
       ["a"%char; "f"%char; "t"%char; "e"%char; "r"%char];
       ["o"%char; "n"%char; "e"%char];
       ["s"%char; "p"%char; "a"%char; "c"%char; "e"%char];
       ["b"%char; "e"%char; "f"%char; "o"%char; "r"%char; "e"%char];
       ["a"%char; "n"%char; "d"%char];
       ["n"%char; "o"%char];
       ["s"%char; "p"%char; "a"%char; "c"%char; "e"%char; "s"%char];
       ["i"%char; "n"%char];
       ["b"%char; "e"%char; "t"%char; "w"%char; "e"%char; "e"%char; "n"%char; "h"%char]
      ] ).
  split.
  - apply wsr_build.
    exact wsar_example_tTwo_spaces_after__one_space_before___and_no_spaces_in_betweenh.
  - simpl. reflexivity.
Qed.