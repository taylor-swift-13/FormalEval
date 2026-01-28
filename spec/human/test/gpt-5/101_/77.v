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

Axiom wsar_example_hOne_two_three_foure_quTickf_the_lazy_dog :
  words_string_aux_rel
    (list_ascii_of_string " hOne,two ,  three , foure quTickf the lazy dog  "%string)
    nil
    ([
      ["h"%char; "O"%char; "n"%char; "e"%char];
      ["t"%char; "w"%char; "o"%char];
      ["t"%char; "h"%char; "r"%char; "e"%char; "e"%char];
      ["f"%char; "o"%char; "u"%char; "r"%char; "e"%char];
      ["q"%char; "u"%char; "T"%char; "i"%char; "c"%char; "k"%char; "f"%char];
      ["t"%char; "h"%char; "e"%char];
      ["l"%char; "a"%char; "z"%char; "y"%char];
      ["d"%char; "o"%char; "g"%char]
    ]).

Example test_problem_101 :
  problem_101_spec " hOne,two ,  three , foure quTickf the lazy dog  "%string
                   ["hOne"%string; "two"%string; "three"%string; "foure"%string; "quTickf"%string; "the"%string; "lazy"%string; "dog"%string].
Proof.
  unfold problem_101_spec.
  exists
    ( [
       ["h"%char; "O"%char; "n"%char; "e"%char];
       ["t"%char; "w"%char; "o"%char];
       ["t"%char; "h"%char; "r"%char; "e"%char; "e"%char];
       ["f"%char; "o"%char; "u"%char; "r"%char; "e"%char];
       ["q"%char; "u"%char; "T"%char; "i"%char; "c"%char; "k"%char; "f"%char];
       ["t"%char; "h"%char; "e"%char];
       ["l"%char; "a"%char; "z"%char; "y"%char];
       ["d"%char; "o"%char; "g"%char]
      ] ).
  split.
  - apply wsr_build.
    exact wsar_example_hOne_two_three_foure_quTickf_the_lazy_dog.
  - simpl. reflexivity.
Qed.