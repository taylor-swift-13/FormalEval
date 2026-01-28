Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List.
Import ListNotations.
Open Scope char_scope.
Open Scope string_scope.

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

Definition problem_101_spec (s : string) (output : list string) : Prop :=
  exists output_list_ascii,
    words_string_rel (list_ascii_of_string s) output_list_ascii /\
    output = map string_of_list_ascii output_list_ascii.

(* Helper Ltac to provide the recurrent steps in the relation proof *)
Ltac solve_words_rel :=
  match goal with
  | |- words_string_aux_rel nil nil nil => constructor
  | |- words_string_aux_rel nil ?cur_word (?cur_word :: nil) =>
      constructor; discriminate
  | |- words_string_aux_rel (?c :: ?cs) nil ?words =>
      first
        [ (* delimiter with empty cur_word *)
          constructor; [ constructor | solve_words_rel ]
        | (* delimiter with non-empty cur_word *)
          constructor; [ constructor | discriminate | solve_words_rel ]
        | (* extend current word by non-delimiter char *)
          let H := fresh "H" in
          assert (~ is_delimiter c) as H by (intro HH; inversion HH);
          constructor 5; [assumption | solve_words_rel]
        ]
  end.

Example problem_101_example :
  problem_101_spec "Hi, my name is John" ["Hi"; "my"; "name"; "is"; "John"].
Proof.
  unfold problem_101_spec.
  exists (
    ["H"; "i"]%char ::
    ["m"; "y"]%char ::
    ["n"; "a"; "m"; "e"]%char ::
    ["i"; "s"]%char ::
    ["J"; "o"; "h"; "n"]%char :: nil).
  split.
  - apply wsr_build.
    (* list_ascii_of_string "Hi, my name is John" = *)
    (* ["H"; "i"; ","; " "; "m"; "y"; " "; "n"; "a"; "m"; "e"; " ";
        "i"; "s"; " "; "J"; "o"; "h"; "n"] *)
    simpl.
    revert ("H" :: "i" :: "," :: " " :: "m" :: "y" :: " " :: "n" :: "a" :: "m" :: "e" :: " " :: "i" :: "s" :: " " :: "J" :: "o" :: "h" :: "n" :: nil)%char.
    intro l.
    revert nil.
    revert (["H"; "i"]%char :: ["m"; "y"]%char :: ["n"; "a"; "m"; "e"]%char :: ["i"; "s"]%char :: ["J"; "o"; "h"; "n"]%char :: nil).
    intros words cur_word chars.
    revert words cur_word chars.
    (* Prove by induction on chars *)
    induction chars as [| c cs IH]; intros words cur_word chars_eq.
    + (* chars = nil *)
      (* We must have words = cur_word :: nil or nil if cur_word=nil *)
      destruct cur_word eqn:CW.
      * simpl in words. subst words.
        apply wsar_empty_empty.
      * simpl in words.
        inversion words; subst.
        apply wsar_empty_word.
        discriminate.
    + (* chars = c :: cs *)
      simpl in words.
      destruct words as [|w ws].
      * (* words = nil impossible if chars nonempty *)
        fail.
      * (* words = w :: ws *)
        (* If c is delimiter *)
        destruct (classic (is_delimiter c)) as [Delim | NonDelim].
        -- (* c is delimiter *)
           destruct cur_word eqn:CW.
           ++ (* cur_word = nil *)
              apply wsar_delim_empty with (cs:=cs) (words:=w::ws) (c:=c).
              ++ (* is_delimiter c *)
                 assumption.
              ++ (* recursive call *)
                 apply IH.
           ++ (* cur_word <> nil; *)
              apply wsar_delim_word with (cs:=cs) (cur_word:=cur_word) (words:=ws) (c:=c).
              ++ assumption.
              ++ discriminate.
              ++ apply IH.
        -- (* c not delimiter *)
           apply wsar_char_extend with (c:=c) (cs:=cs) (cur_word:=cur_word) (words:=w::ws).
           ++ assumption.
           ++ apply IH.
Qed.