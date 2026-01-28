Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool Coq.ZArith.ZArith.
Import ListNotations.

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
    output = map string_of_list_ascii output_list_ascii.

Lemma count_nil_zero : forall n, count_consonants_rel nil n -> n = 0%nat.
Proof.
  intros n H. inversion H; auto.
Qed.

Lemma count_singleton : forall c m, count_consonants_rel [c] m -> m = 0%nat \/ m = 1%nat.
Proof.
  intros c m H. inversion H; subst.
  - (* consonant, tail nil *)
    inversion H2; subst.
    right. reflexivity.
  - (* vowel, tail nil *)
    inversion H2; subst.
    left. reflexivity.
  - (* not letter, tail nil *)
    inversion H1; subst.
    left. reflexivity.
Qed.

Lemma single_letter_not_four : forall c, ~ count_consonants_rel [c] 4%nat.
Proof.
  intros c H.
  apply count_singleton in H.
  destruct H; lia.
Qed.

Lemma is_letter_lower_l : is_letter "l"%char.
Proof.
  apply il_lower. simpl. split; lia.
Qed.

Lemma is_letter_lower_t : is_letter "t"%char.
Proof.
  apply il_lower. simpl. split; lia.
Qed.

Lemma is_letter_lower_i : is_letter "i"%char.
Proof.
  apply il_lower. simpl. split; lia.
Qed.

Lemma is_letter_lower_e : is_letter "e"%char.
Proof.
  apply il_lower. simpl. split; lia.
Qed.

Lemma not_vowel_l : ~ is_vowel "l"%char.
Proof.
  intros H. inversion H.
Qed.

Lemma not_vowel_t : ~ is_vowel "t"%char.
Proof.
  intros H. inversion H.
Qed.

Lemma count_little_4 : count_consonants_rel (list_ascii_of_string "little") 4%nat.
Proof.
  simpl.
  eapply ccr_consonant.
  - apply is_letter_lower_l.
  - apply not_vowel_l.
  - simpl.
    eapply ccr_vowel.
    + apply is_letter_lower_i.
    + constructor.
    + simpl.
      eapply ccr_consonant.
      * apply is_letter_lower_t.
      * apply not_vowel_t.
      * simpl.
        eapply ccr_consonant.
        -- apply is_letter_lower_t.
        -- apply not_vowel_t.
        -- simpl.
           eapply ccr_consonant.
           ++ apply is_letter_lower_l.
           ++ apply not_vowel_l.
           ++ simpl.
              eapply ccr_vowel.
              ** apply is_letter_lower_e.
              ** constructor.
              ** apply ccr_nil.
Qed.

Example problem_117_test1 :
  problem_117_spec "Mary had a little lamb" (Z.to_nat 4%Z) ["little"].
Proof.
  unfold problem_117_spec.
  exists
    [ list_ascii_of_string "M"
    ; list_ascii_of_string "a"
    ; list_ascii_of_string "r"
    ; list_ascii_of_string "y"
    ; list_ascii_of_string "h"
    ; list_ascii_of_string "a"
    ; list_ascii_of_string "d"
    ; list_ascii_of_string "a"
    ; list_ascii_of_string "little"
    ; list_ascii_of_string "i"
    ; list_ascii_of_string "t"
    ; list_ascii_of_string "t"
    ; list_ascii_of_string "l"
    ; list_ascii_of_string "e"
    ; list_ascii_of_string "l"
    ; list_ascii_of_string "a"
    ; list_ascii_of_string "m"
    ; list_ascii_of_string "b"
    ].
  exists [list_ascii_of_string "little"].
  split.
  - simpl.
    (* "M" *)
    apply (swr_char "M"%char _ nil _); [simpl; reflexivity|].
    (* "a" *)
    apply (swr_char "a"%char _ nil _); [simpl; reflexivity|].
    (* "r" *)
    apply (swr_char "r"%char _ nil _); [simpl; reflexivity|].
    (* "y" *)
    apply (swr_char "y"%char _ nil _); [simpl; reflexivity|].
    (* space *)
    apply (swr_space_new " "%char); [simpl; reflexivity|].
    (* "h" *)
    apply (swr_char "h"%char _ nil _); [simpl; reflexivity|].
    (* "a" *)
    apply (swr_char "a"%char _ nil _); [simpl; reflexivity|].
    (* "d" *)
    apply (swr_char "d"%char _ nil _); [simpl; reflexivity|].
    (* space *)
    apply (swr_space_new " "%char); [simpl; reflexivity|].
    (* "a" *)
    apply (swr_char "a"%char _ nil _); [simpl; reflexivity|].
    (* space *)
    apply (swr_space_new " "%char); [simpl; reflexivity|].
    (* "l" -> "little" *)
    apply (swr_char "l"%char _ (list_ascii_of_string "ittle") _); [simpl; reflexivity|].
    (* "i" *)
    apply (swr_char "i"%char _ nil _); [simpl; reflexivity|].
    (* "t" *)
    apply (swr_char "t"%char _ nil _); [simpl; reflexivity|].
    (* "t" *)
    apply (swr_char "t"%char _ nil _); [simpl; reflexivity|].
    (* "l" *)
    apply (swr_char "l"%char _ nil _); [simpl; reflexivity|].
    (* "e" *)
    apply (swr_char "e"%char _ nil _); [simpl; reflexivity|].
    (* space *)
    apply (swr_space_new " "%char); [simpl; reflexivity|].
    (* "l" *)
    apply (swr_char "l"%char _ nil _); [simpl; reflexivity|].
    (* "a" *)
    apply (swr_char "a"%char _ nil _); [simpl; reflexivity|].
    (* "m" *)
    apply (swr_char "m"%char _ nil _); [simpl; reflexivity|].
    (* "b" *)
    apply (swr_char "b"%char _ nil _); [simpl; reflexivity|].
    (* end *)
    apply swr_nil.
  - split.
    + (* selection: only "little" matches 4 consonants *)
      eapply swsel_no_match.
      * apply single_letter_not_four.
      * eapply swsel_no_match.
        -- apply single_letter_not_four.
        -- eapply swsel_no_match.
           ++ apply single_letter_not_four.
           ++ eapply swsel_no_match.
              ** apply single_letter_not_four.
              ** eapply swsel_no_match.
                 --- apply single_letter_not_four.
                 --- eapply swsel_no_match.
                     +++ apply single_letter_not_four.
                     +++ eapply swsel_no_match.
                         *** apply single_letter_not_four.
                         *** eapply swsel_no_match.
                             ---- apply single_letter_not_four.
                             ---- eapply swsel_match.
                                  + apply count_little_4.
                                  + eapply swsel_no_match.
                                    * apply single_letter_not_four.
                                    * eapply swsel_no_match.
                                      { apply single_letter_not_four. }
                                      { eapply swsel_no_match.
                                          - apply single_letter_not_four.
                                          - eapply swsel_no_match.
                                            + apply single_letter_not_four.
                                            + eapply swsel_no_match.
                                              * apply single_letter_not_four.
                                              * eapply swsel_no_match.
                                                { apply single_letter_not_four. }
                                                { eapply swsel_no_match.
                                                    - apply single_letter_not_four.
                                                    - eapply swsel_no_match.
                                                      + apply single_letter_not_four.
                                                      + eapply swsel_no_match.
                                                        * apply single_letter_not_four.
                                                        * apply swsel_nil. }
                                      }
    + simpl. reflexivity.
Qed.