Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.

(* Provided predicates and inductive relations *)

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

(* Explicit ascii list of "Mary had a little lamb" *)

Definition mary_str := "Mary had a little lamb".

Definition mary_ascii := list_ascii_of_string mary_str.

(* Let's build the words manually as ascii lists *)

Definition word_Mary := ["M"%char;"a"%char;"r"%char;"y"%char].
Definition word_had := ["h"%char;"a"%char;"d"%char].
Definition word_a := ["a"%char].
Definition word_little := ["l"%char;"i"%char;"t"%char;"t"%char;"l"%char;"e"%char].
Definition word_lamb := ["l"%char;"a"%char;"m"%char;"b"%char].

(* We begin by constructing the split_words_rel proof.
   split_words_rel splits the string at spaces, keeping words reversed during processing.
   Here, the words appear in input order. We proceed assuming split_words_rel produces
   the list of words in the order: [word_Mary; word_had; word_a; word_little; word_lamb]. *)

Lemma split_words_mary :
  split_words_rel mary_ascii [word_Mary; word_had; word_a; word_little; word_lamb].
Proof.
  unfold mary_ascii, word_Mary, word_had, word_a, word_little, word_lamb.
  unfold mary_str.
  (* We unfold list_ascii_of_string to the ascii list for the string "Mary had a little lamb". *)
  (* List ascii of "Mary had a little lamb": *)
  (* "M", "a", "r", "y", " ", "h", "a", "d", " ", "a", " ", "l", "i", "t", "t", "l", "e", " ", "l", "a", "m", "b" *)
  (* Let's apply swr_char and swr_space_finish step by step *)

  eapply swr_char. (* 'M' *)
  eapply swr_char. (* 'a' *)
  eapply swr_char. (* 'r' *)
  eapply swr_char. (* 'y' *)
  eapply swr_space_finish. 1: discriminate. (* space finished word: "Mary" *)

  eapply swr_char. (* 'h' *)
  eapply swr_char. (* 'a' *)
  eapply swr_char. (* 'd' *)
  eapply swr_space_finish. 1: discriminate. (* space finishes "had" *)

  eapply swr_char. (* 'a' *)
  eapply swr_space_finish. 1: discriminate. (* space finishes "a" *)

  eapply swr_char. (* 'l' *)
  eapply swr_char. (* 'i' *)
  eapply swr_char. (* 't' *)
  eapply swr_char. (* 't' *)
  eapply swr_char. (* 'l' *)
  eapply swr_char. (* 'e' *)
  eapply swr_space_finish. 1: discriminate. (* space finishes "little" *)

  eapply swr_char. (* 'l' *)
  eapply swr_char. (* 'a' *)
  eapply swr_char. (* 'm' *)
  eapply swr_char. (* 'b' *)
  eapply swr_nil.
Qed.

(* Proofs of count_consonants_rel for the chosen words *)

Lemma count_consonants_Mary : count_consonants_rel word_Mary 3.
Proof.
  eapply ccr_consonant.
  - constructor. simpl. lia. (* 'M' uppercase letter *)
  - intro H; inversion H.
  - eapply ccr_vowel.
    + constructor. simpl. lia. (* 'a' vowel *)
    + apply iv_a.
    + eapply ccr_consonant.
      * constructor. simpl. lia. (* 'r' consonant *)
      * intro H; inversion H.
      * eapply ccr_consonant.
        -- constructor. simpl. lia. (* 'y' consonant *)
        -- intro H; inversion H.
        -- eapply ccr_nil.
Qed.

Lemma count_consonants_had : count_consonants_rel word_had 2.
Proof.
  eapply ccr_consonant.
  - constructor. simpl. lia. (* 'h' consonant *)
  - intro H; inversion H.
  - eapply ccr_vowel.
    + constructor. simpl. lia. (* 'a' vowel *)
    + apply iv_a.
    + eapply ccr_consonant.
      * constructor. simpl. lia. (* 'd' consonant *)
      * intro H; inversion H.
      * eapply ccr_nil.
Qed.

Lemma count_consonants_a : count_consonants_rel word_a 0.
Proof.
  eapply ccr_vowel.
  - constructor. simpl. lia. (* 'a' vowel *)
  - apply iv_a.
  - eapply ccr_nil.
Qed.

Lemma count_consonants_little : count_consonants_rel word_little 4.
Proof.
  eapply ccr_consonant.
  - constructor. simpl. lia. (* 'l' consonant *)
  - intro H; inversion H.
  - eapply ccr_vowel.
    + constructor. simpl. lia. (* 'i' vowel *)
    + apply iv_i.
    + eapply ccr_consonant.
      * constructor. simpl. lia. (* 't' consonant *)
      * intro H; inversion H.
      * eapply ccr_consonant.
        -- constructor. simpl. lia. (* 't' consonant *)
        -- intro H; inversion H.
        -- eapply ccr_consonant.
           ++ constructor. simpl. lia. (* 'l' consonant *)
           ++ intro H; inversion H.
           ++ eapply ccr_vowel.
              ** constructor. simpl. lia. (* 'e' vowel *)
              ** apply iv_e.
              ** eapply ccr_nil.
Qed.

Lemma count_consonants_lamb : count_consonants_rel word_lamb 3.
Proof.
  eapply ccr_consonant.
  - constructor. simpl. lia. (* 'l' consonant *)
  - intro H; inversion H.
  - eapply ccr_vowel.
    + constructor. simpl. lia. (* 'a' vowel *)
    + apply iv_a.
    + eapply ccr_consonant.
      * constructor. simpl. lia. (* 'm' consonant *)
      * intro H; inversion H.
      * eapply ccr_consonant.
        -- constructor. simpl. lia. (* 'b' consonant *)
        -- intro H; inversion H.
        -- eapply ccr_nil.
Qed.

(* select_words_rel for input words at n = 4 producing ["little"] *)

Lemma select_words_4_little :
  select_words_rel
    [word_Mary; word_had; word_a; word_little; word_lamb]
    4
    [word_little].
Proof.
  eapply swsel_no_match.
  - intro H; inversion H. (* Mary has 3, not 4 *)
  - eapply swsel_no_match.
    + intro H; inversion H. (* had 2 *)
    + eapply swsel_no_match.
      * intro H; inversion H. (* a 0 *)
      * eapply swsel_match.
        -- apply count_consonants_little.
        -- eapply swsel_no_match.
           ++ intro H; inversion H. (* lamb 3 *)
           ++ eapply swsel_nil.
Qed.

(* Final theorem that combines all parts *)

Example test_select_words_little :
  problem_117_spec "Mary had a little lamb" 4 ["little"].
Proof.
  unfold problem_117_spec.
  exists [word_Mary; word_had; word_a; word_little; word_lamb].
  exists [word_little].
  split.
  - apply split_words_mary.
  split.
  - apply select_words_4_little.
  - simpl.
    (* map string_of_list_ascii produces ["little"], reflexivity applies *)
    reflexivity.
Qed.