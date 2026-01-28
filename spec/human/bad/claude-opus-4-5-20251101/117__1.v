Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Require Import Lia.
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

(* Helper lemmas for proving is_letter *)
Lemma is_letter_M : is_letter "M"%char.
Proof. apply il_upper. simpl. split; lia. Qed.

Lemma is_letter_a : is_letter "a"%char.
Proof. apply il_lower. simpl. split; lia. Qed.

Lemma is_letter_r : is_letter "r"%char.
Proof. apply il_lower. simpl. split; lia. Qed.

Lemma is_letter_y : is_letter "y"%char.
Proof. apply il_lower. simpl. split; lia. Qed.

Lemma is_letter_h : is_letter "h"%char.
Proof. apply il_lower. simpl. split; lia. Qed.

Lemma is_letter_d : is_letter "d"%char.
Proof. apply il_lower. simpl. split; lia. Qed.

Lemma is_letter_l : is_letter "l"%char.
Proof. apply il_lower. simpl. split; lia. Qed.

Lemma is_letter_i : is_letter "i"%char.
Proof. apply il_lower. simpl. split; lia. Qed.

Lemma is_letter_t : is_letter "t"%char.
Proof. apply il_lower. simpl. split; lia. Qed.

Lemma is_letter_e : is_letter "e"%char.
Proof. apply il_lower. simpl. split; lia. Qed.

Lemma is_letter_m : is_letter "m"%char.
Proof. apply il_lower. simpl. split; lia. Qed.

Lemma is_letter_b : is_letter "b"%char.
Proof. apply il_lower. simpl. split; lia. Qed.

(* Helper lemmas for not vowels *)
Lemma not_vowel_M : ~ is_vowel "M"%char.
Proof. intro H; inversion H. Qed.

Lemma not_vowel_r : ~ is_vowel "r"%char.
Proof. intro H; inversion H. Qed.

Lemma not_vowel_y : ~ is_vowel "y"%char.
Proof. intro H; inversion H. Qed.

Lemma not_vowel_h : ~ is_vowel "h"%char.
Proof. intro H; inversion H. Qed.

Lemma not_vowel_d : ~ is_vowel "d"%char.
Proof. intro H; inversion H. Qed.

Lemma not_vowel_l : ~ is_vowel "l"%char.
Proof. intro H; inversion H. Qed.

Lemma not_vowel_t : ~ is_vowel "t"%char.
Proof. intro H; inversion H. Qed.

Lemma not_vowel_m : ~ is_vowel "m"%char.
Proof. intro H; inversion H. Qed.

Lemma not_vowel_b : ~ is_vowel "b"%char.
Proof. intro H; inversion H. Qed.

(* Count consonants for "little" = 4 *)
Lemma count_little : count_consonants_rel ["l"; "i"; "t"; "t"; "l"; "e"]%char 4.
Proof.
  apply ccr_consonant; [apply is_letter_l | apply not_vowel_l |].
  apply ccr_vowel; [apply is_letter_i | apply iv_i |].
  apply ccr_consonant; [apply is_letter_t | apply not_vowel_t |].
  apply ccr_consonant; [apply is_letter_t | apply not_vowel_t |].
  apply ccr_consonant; [apply is_letter_l | apply not_vowel_l |].
  apply ccr_vowel; [apply is_letter_e | apply iv_e |].
  apply ccr_nil.
Qed.

(* Count consonants for "Mary" = 3 *)
Lemma count_Mary_3 : count_consonants_rel ["M"; "a"; "r"; "y"]%char 3.
Proof.
  apply ccr_consonant; [apply is_letter_M | apply not_vowel_M |].
  apply ccr_vowel; [apply is_letter_a | apply iv_a |].
  apply ccr_consonant; [apply is_letter_r | apply not_vowel_r |].
  apply ccr_consonant; [apply is_letter_y | apply not_vowel_y |].
  apply ccr_nil.
Qed.

(* Count consonants for "had" = 2 *)
Lemma count_had_2 : count_consonants_rel ["h"; "a"; "d"]%char 2.
Proof.
  apply ccr_consonant; [apply is_letter_h | apply not_vowel_h |].
  apply ccr_vowel; [apply is_letter_a | apply iv_a |].
  apply ccr_consonant; [apply is_letter_d | apply not_vowel_d |].
  apply ccr_nil.
Qed.

(* Count consonants for "a" = 0 *)
Lemma count_a_0 : count_consonants_rel ["a"]%char 0.
Proof.
  apply ccr_vowel; [apply is_letter_a | apply iv_a |].
  apply ccr_nil.
Qed.

(* Count consonants for "lamb" = 3 *)
Lemma count_lamb_3 : count_consonants_rel ["l"; "a"; "m"; "b"]%char 3.
Proof.
  apply ccr_consonant; [apply is_letter_l | apply not_vowel_l |].
  apply ccr_vowel; [apply is_letter_a | apply iv_a |].
  apply ccr_consonant; [apply is_letter_m | apply not_vowel_m |].
  apply ccr_consonant; [apply is_letter_b | apply not_vowel_b |].
  apply ccr_nil.
Qed.

(* Uniqueness of count_consonants_rel *)
Lemma count_consonants_unique : forall l n1 n2,
  count_consonants_rel l n1 -> count_consonants_rel l n2 -> n1 = n2.
Proof.
  intros l n1 n2 H1.
  generalize dependent n2.
  induction H1; intros n2 H2.
  - inversion H2; reflexivity.
  - inversion H2; subst.
    + f_equal. apply IHcount_consonants_rel. assumption.
    + contradiction.
    + contradiction.
  - inversion H2; subst.
    + contradiction.
    + apply IHcount_consonants_rel. assumption.
    + contradiction.
  - inversion H2; subst.
    + contradiction.
    + contradiction.
    + apply IHcount_consonants_rel. assumption.
Qed.

Lemma not_count_Mary_4 : ~ count_consonants_rel ["M"; "a"; "r"; "y"]%char 4.
Proof.
  intro H.
  assert (H3: count_consonants_rel ["M"; "a"; "r"; "y"]%char 3) by apply count_Mary_3.
  pose proof (count_consonants_unique _ _ _ H H3).
  discriminate.
Qed.

Lemma not_count_had_4 : ~ count_consonants_rel ["h"; "a"; "d"]%char 4.
Proof.
  intro H.
  assert (H2: count_consonants_rel ["h"; "a"; "d"]%char 2) by apply count_had_2.
  pose proof (count_consonants_unique _ _ _ H H2).
  discriminate.
Qed.

Lemma not_count_a_4 : ~ count_consonants_rel ["a"]%char 4.
Proof.
  intro H.
  assert (H0: count_consonants_rel ["a"]%char 0) by apply count_a_0.
  pose proof (count_consonants_unique _ _ _ H H0).
  discriminate.
Qed.

Lemma not_count_lamb_4 : ~ count_consonants_rel ["l"; "a"; "m"; "b"]%char 4.
Proof.
  intro H.
  assert (H3: count_consonants_rel ["l"; "a"; "m"; "b"]%char 3) by apply count_lamb_3.
  pose proof (count_consonants_unique _ _ _ H H3).
  discriminate.
Qed.

Example test_problem_117 :
  problem_117_spec "Mary had a little lamb" 4 ["little"%string].
Proof.
  unfold problem_117_spec.
  exists [["M"; "a"; "r"; "y"]; ["h"; "a"; "d"]; ["a"]; ["l"; "i"; "t"; "t"; "l"; "e"]; ["l"; "a"; "m"; "b"]]%char.
  exists [["l"; "i"; "t"; "t"; "l"; "e"]]%char.
  split; [| split].
  - simpl.
    apply swr_char. reflexivity.
    apply swr_char. reflexivity.
    apply swr_char. reflexivity.
    apply swr_char. reflexivity.
    apply swr_space_finish. reflexivity. discriminate.
    apply swr_char. reflexivity.
    apply swr_char. reflexivity.
    apply swr_char. reflexivity.
    apply swr_space_finish. reflexivity. discriminate.
    apply swr_char. reflexivity.
    apply swr_space_finish. reflexivity. discriminate.
    apply swr_char. reflexivity.
    apply swr_char. reflexivity.
    apply swr_char. reflexivity.
    apply swr_char. reflexivity.
    apply swr_char. reflexivity.
    apply swr_char. reflexivity.
    apply swr_space_finish. reflexivity. discriminate.
    apply swr_char. reflexivity.
    apply swr_char. reflexivity.
    apply swr_char. reflexivity.
    apply swr_char. reflexivity.
    apply swr_nil.
  - apply swsel_no_match; [apply not_count_Mary_4 |].
    apply swsel_no_match; [apply not_count_had_4 |].
    apply swsel_no_match; [apply not_count_a_4 |].
    apply swsel_match; [apply count_little |].
    apply swsel_no_match; [apply not_count_lamb_4 |].
    apply swsel_nil.
  - reflexivity.
Qed.