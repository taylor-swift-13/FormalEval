Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool Coq.omega.Omega.
Import ListNotations.

(* Helper functions required for the specification *)
Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => nil
  | String c s' => c :: list_ascii_of_string s'
  end.

Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | nil => EmptyString
  | c :: l' => String c (string_of_list_ascii l')
  end.

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

Definition problem_117_spec (s : string) (n : nat) (output : list string) : Prop :=
  exists words output_list_ascii,
    split_words_rel (list_ascii_of_string s) words /\
    select_words_rel words n output_list_ascii /\
    output = map string_of_list_ascii output_list_ascii.

(* Tactics *)
Ltac prove_is_letter :=
  first [ apply il_lower; simpl; omega | apply il_upper; simpl; omega ].

Ltac prove_is_vowel :=
  first [ apply iv_a | apply iv_e | apply iv_i | apply iv_o | apply iv_u |
          apply iv_A | apply iv_E | apply iv_I | apply iv_O | apply iv_U ].

Ltac prove_not_vowel :=
  let H := fresh in
  intro H; inversion H.

Ltac prove_count :=
  repeat match goal with
  | |- count_consonants_rel nil 0 => apply ccr_nil
  | |- count_consonants_rel (_ :: _) (S _) =>
      apply ccr_consonant; [ prove_is_letter | prove_not_vowel | ]
  | |- count_consonants_rel (_ :: _) _ =>
      apply ccr_vowel; [ prove_is_letter | prove_is_vowel | ]
  end.

Ltac prove_not_count :=
  intro H;
  repeat match goal with
  | H : count_consonants_rel _ _ |- _ => inversion H; subst; clear H
  | H : is_letter _ |- _ => inversion H; subst; clear H; simpl in *
  | H : is_vowel _ |- _ => inversion H
  | H : ~ is_vowel _ |- _ => exfalso; apply H; prove_is_vowel
  | H : ~ is_letter _ |- _ => exfalso; apply H; prove_is_letter
  end;
  try (simpl in *; omega).

Ltac solve_split :=
  repeat match goal with
  | |- split_words_rel nil nil => apply swr_nil
  | |- split_words_rel (" "%char :: _) _ => apply swr_space_new; [reflexivity | ]
  | |- split_words_rel (?c :: _) _ => apply swr_char; [reflexivity | ]
  end.

Example test_problem_117 : problem_117_spec "Mary had a little lamb" 4 ["little"%string].
Proof.
  unfold problem_117_spec.
  exists [
    list_ascii_of_string "Mary";
    list_ascii_of_string "had";
    list_ascii_of_string "a";
    list_ascii_of_string "little";
    list_ascii_of_string "lamb"
  ].
  exists [list_ascii_of_string "little"].
  
  split.
  - (* Prove split_words_rel *)
    (* We use the strategy where swr_char consumes the head word one char at a time,
       and swr_space_new skips spaces between words. *)
    solve_split.
  - split.
    + (* Prove select_words_rel *)
      (* Mary (3 != 4) *) apply swsel_no_match. prove_not_count.
      (* had (2 != 4) *) apply swsel_no_match. prove_not_count.
      (* a (0 != 4) *) apply swsel_no_match. prove_not_count.
      (* little (4 == 4) *) apply swsel_match. prove_count.
      (* lamb (3 != 4) *) apply swsel_no_match. prove_not_count.
      apply swsel_nil.
    
    + (* Prove output mapping *)
      simpl. reflexivity.
Qed.