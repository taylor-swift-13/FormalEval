Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.

Open Scope string_scope.

Inductive is_vowel : ascii -> Prop :=
| iv_a : is_vowel "a"%char
| iv_e : is_vowel "e"%char
| iv_i : is_vowel "i"%char
| iv_o : is_vowel "o"%char
| iv_u : is_vowel "u"%char
| iv_A : is_vowel "A"%char
| iv_E : is_vowel "E"%char
| iv_I : is_vowel "I"%char
| iv_O : is_vowel "O"%char
| iv_U : is_vowel "U"%char.

Inductive is_letter : ascii -> Prop :=
| il_upper : forall c, let n := nat_of_ascii c in (65 <= n /\ n <= 90) -> is_letter c
| il_lower : forall c, let n := nat_of_ascii c in (97 <= n /\ n <= 122) -> is_letter c.

Inductive count_consonants_rel : list ascii -> nat -> Prop :=
| ccr_nil : count_consonants_rel nil 0%nat
| ccr_consonant : forall h t n, is_letter h -> ~ is_vowel h -> count_consonants_rel t n ->
    count_consonants_rel (h :: t) (S n)
| ccr_vowel : forall h t n, is_letter h -> is_vowel h -> count_consonants_rel t n ->
    count_consonants_rel (h :: t) n
| ccr_not_letter : forall h t n, ~ is_letter h -> count_consonants_rel t n ->
    count_consonants_rel (h :: t) n.

Inductive split_words_rel : list ascii -> list (list ascii) -> Prop :=
| swr_nil : split_words_rel nil nil
| swr_space_new : forall c cs words, Ascii.eqb c " "%char = true ->
    split_words_rel cs words ->
    split_words_rel (c :: cs) words
| swr_space_finish : forall c cs cur words, Ascii.eqb c " "%char = true ->
    cur <> nil -> split_words_rel cs words ->
    split_words_rel (c :: cs) ((rev cur) :: words)
| swr_char : forall c cs cur words, Ascii.eqb c " "%char = false ->
    split_words_rel cs words ->
    split_words_rel (c :: cs) ((c :: cur) :: words).

Inductive select_words_rel : list (list ascii) -> nat -> list (list ascii) -> Prop :=
| swsel_nil : forall n, select_words_rel nil n nil
| swsel_match : forall w ws n res, count_consonants_rel w n ->
    select_words_rel ws n res ->
    select_words_rel (w :: ws) n (w :: res)
| swsel_no_match : forall w ws n res, ~ (count_consonants_rel w n) ->
    select_words_rel ws n res ->
    select_words_rel (w :: ws) n res.

Definition problem_117_pre (s : string) : Prop :=
  let l := list_ascii_of_string s in
  Forall (fun c => c = " "%char \/ let n := nat_of_ascii c in (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122)) l.

Definition problem_117_spec (s : string) (n : nat) (output : list string) : Prop :=
  exists words output_list_ascii,
    split_words_rel (list_ascii_of_string s) words /\
    select_words_rel words n output_list_ascii /\
    output = map string_of_list_ascii (rev output_list_ascii).

Example example_117 : problem_117_spec "Mary had a little lamb" 4 ["little"].
Proof.
  unfold problem_117_spec.
  exists [["M"; "a"; "r"; "y"]; ["h"; "a"; "d"]; ["a"]; ["l"; "i"; "t"; "t"; "l"; "e"]; ["l"; "a"; "m"; "b"]],
         [["l"; "i"; "t"; "t"; "l"; "e"]].
  split.
  - apply swr_char with (cur := []).
    + reflexivity.
    + apply swr_char with (cur := ["M"]).
      * reflexivity.
      * apply swr_char with (cur := ["a"; "M"]).
        -- reflexivity.
        -- apply swr_char with (cur := ["r"; "a"; "M"]).
           ++ reflexivity.
           ++ apply swr_char with (cur := ["y"; "r"; "a"; "M"]).
              ** reflexivity.
              ** apply swr_space_finish.
                 --- reflexivity.
                 --- discriminate.
                 --- apply swr_char with (cur := []).
                     +++ reflexivity.
                     +++ apply swr_char with (cur := ["h"]).
                         *** reflexivity.
                         *** apply swr_char with (cur := ["a"; "h"]).
                             ---- reflexivity.
                             ---- apply swr_char with (cur := ["d"; "a"; "h"]).
                                  +++++ reflexivity.
                                  +++++ apply swr_space_finish.
                                        ***** reflexivity.
                                        ***** discriminate.
                                        ***** apply swr_space_new.
                                              { reflexivity. }
                                              { apply swr_char with (cur := []).
                                                  - reflexivity.
                                                  - apply swr_space_finish.
                                                    + reflexivity.
                                                    + discriminate.
                                                    + apply swr_char with (cur := []).
                                                      * reflexivity.
                                                      * apply swr_char with (cur := ["l"]).
                                                        ** reflexivity.
                                                        ** apply swr_char with (cur := ["i"; "l"]).
                                                           --- reflexivity.
                                                           --- apply swr_char with (cur := ["t"; "i"; "l"]).
                                                               +++ reflexivity.
                                                               +++ apply swr_char with (cur := ["t"; "t"; "i"; "l"]).
                                                                   *** reflexivity.
                                                                   *** apply swr_char with (cur := ["l"; "t"; "t"; "i"; "l"]).
                                                                       ---- reflexivity.
                                                                       ---- apply swr_char with (cur := ["e"; "l"; "t"; "t"; "i"; "l"]).
                                                                            +++++ reflexivity.
                                                                            +++++ apply swr_space_finish.
                                                                                  ***** reflexivity.
                                                                                  ***** discriminate.
                                                                                  ***** apply swr_char with (cur := []).
                                                                                        { reflexivity. }
                                                                                        { apply swr_char with (cur := ["l"]).
                                                                                            - reflexivity.
                                                                                            - apply swr_char with (cur := ["a"; "l"]).
                                                                                              + reflexivity.
                                                                                              + apply swr_char with (cur := ["m"; "a"; "l"]).
                                                                                                * reflexivity.
                                                                                                * apply swr_char with (cur := ["b"; "m"; "a"; "l"]).
                                                                                                  -- reflexivity.
                                                                                                  -- apply swr_nil.
  - split.
    + apply swsel_match.
      * apply ccr_consonant.
        -- apply il_lower. compute. auto.
        -- intro H. inversion H.
        -- apply ccr_consonant.
           ++ apply il_lower. compute. auto.
           ++ intro H. inversion H.
           ++ apply ccr_consonant.
              ** apply il_lower. compute. auto.
              ** intro H. inversion H.
              ** apply ccr_consonant.
                 --- apply il_lower. compute. auto.
                 --- intro H. inversion H.
                 --- apply ccr_nil.
      * apply swsel_no_match.
        -- intro H. inversion H.
        -- apply swsel_no_match.
           ++ intro H. inversion H.
           ++ apply swsel_no_match.
              ** intro H. inversion H.
              ** apply swsel_no_match.
                 --- intro H. inversion H.
                 --- apply swsel_nil.
    + reflexivity.
Qed.