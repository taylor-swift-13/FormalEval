Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.Arith Coq.Bool.Bool Coq.Arith.PeanoNat.
Import ListNotations.

(* Definitions from the problem *)

Inductive has_divisor_from_rel : nat -> nat -> Prop :=
| hdfr_base : forall n d, n mod d = 0 -> d > 1 -> has_divisor_from_rel n d
| hdfr_step : forall n d, has_divisor_from_rel n (S d) -> has_divisor_from_rel n d.

Inductive is_prime_rel : nat -> Prop :=
| ipr_prime : forall n,
    n > 1 ->
    ~ (exists d, 2 <= d <= n - 1 /\ has_divisor_from_rel n d) ->
    is_prime_rel n.

Inductive split_words_aux_rel : list ascii -> list ascii -> list (list ascii) -> Prop :=
| swar_nil_empty : split_words_aux_rel nil nil nil
| swar_nil_word : forall cur, cur <> nil -> split_words_aux_rel nil cur ((rev cur) :: nil)
| swar_space_skip : forall cs words_rev,
    split_words_aux_rel cs nil words_rev ->
    split_words_aux_rel (" "%char :: cs) nil words_rev
| swar_space_finish : forall cs cur words_rev,
    cur <> nil ->
    split_words_aux_rel cs nil words_rev ->
    split_words_aux_rel (" "%char :: cs) cur ((rev cur) :: words_rev)
| swar_char : forall c cs cur words_rev,
    Ascii.eqb c " "%char = false ->
    split_words_aux_rel cs (c :: cur) words_rev ->
    split_words_aux_rel (c :: cs) cur words_rev.

Inductive split_words_rel : list ascii -> list (list ascii) -> Prop :=
| swr_build : forall s words_rev words,
    split_words_aux_rel s nil words_rev ->
    words = rev words_rev ->
    split_words_rel s words.

Inductive filter_prime_length_rel : list (list ascii) -> list (list ascii) -> Prop :=
| fplr_nil : filter_prime_length_rel nil nil
| fplr_keep : forall w ws res,
    is_prime_rel (length w) ->
    filter_prime_length_rel ws res ->
    filter_prime_length_rel (w :: ws) (w :: res)
| fplr_drop : forall w ws res,
    ~ is_prime_rel (length w) ->
    filter_prime_length_rel ws res ->
    filter_prime_length_rel (w :: ws) res.

Inductive join_words_rel : list (list ascii) -> list ascii -> Prop :=
| jwr_nil : join_words_rel nil nil
| jwr_single : forall w, join_words_rel (w :: nil) w
| jwr_multi : forall w ws res,
    join_words_rel ws res ->
    join_words_rel (w :: ws) (w ++ (" "%char :: nil) ++ res).

Definition problem_143_pre (sentence : string) : Prop :=
  let l := list_ascii_of_string sentence in
  1 <= length l /\ length l <= 100 /\
  Forall (fun c =>
    let n := nat_of_ascii c in c = " "%char \/ (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122)) l.

Definition problem_143_spec (sentence : string) (output : string) : Prop :=
  exists words filtered,
    split_words_rel (list_ascii_of_string sentence) words /\
    filter_prime_length_rel words filtered /\
    join_words_rel filtered (list_ascii_of_string output).

(* Primality lemmas *)

Lemma prime_two : is_prime_rel 2.
Proof.
  constructor.
  - lia.
  - unfold not; intros [d [H1 [H2 _]]].
    destruct d; lia.
Qed.

Lemma prime_three : is_prime_rel 3.
Proof.
  constructor.
  - lia.
  - unfold not; intros [d [H1 [H2 _]]].
    destruct d; lia.
Qed.

Lemma not_prime_one : ~ is_prime_rel 1.
Proof.
  intros H; inversion H; lia.
Qed.

Lemma not_prime_four : ~ is_prime_rel 4.
Proof.
  intros H.
  inversion H as [_ _ Hnp].
  specialize (Hnp 2).
  assert (2 <= 3 /\ 2 <= 3) by lia.
  assert (has_divisor_from_rel 4 2).
  { apply hdfr_base. reflexivity. lia. }
  apply Hnp; eauto.
Qed.

(* Define ascii lists for words in "This is a test" *)

Definition ascii_This := list_ascii_of_string "This".
Definition ascii_is := list_ascii_of_string "is".
Definition ascii_a := list_ascii_of_string "a".
Definition ascii_test := list_ascii_of_string "test".

(* Split "This is a test" into words *)

Lemma split_words_This_is_a_test :
  split_words_rel (list_ascii_of_string "This is a test")
                  [ascii_This; ascii_is; ascii_a; ascii_test].
Proof.
  remember (list_ascii_of_string "This is a test") as s eqn:Hs.
  (* We construct words_rev := rev ascii_test :: rev ascii_a :: rev ascii_is :: rev ascii_This :: nil *)
  assert (Haux: split_words_aux_rel s nil
            (rev ascii_test :: rev ascii_a :: rev ascii_is :: rev ascii_This :: nil)).
  {
    subst s.
    eapply swar_char; last apply swar_char; last apply swar_char; last apply swar_char;
    try (simpl; reflexivity).
    - (* 'T' *)
      eapply swar_space_finish; [ | eapply swar_char; eapply swar_char; eapply swar_char; eapply swar_space_finish; [discriminate | ]].
      + discriminate.
      + eapply swar_space_finish; [ | eapply swar_char; eapply swar_space_finish; [discriminate | eapply swar_nil_word]].
        * discriminate.
        * discriminate.
  }
  exists [ascii_This; ascii_is; ascii_a; ascii_test].
  apply swr_build with (words_rev := (rev ascii_test :: rev ascii_a :: rev ascii_is :: rev ascii_This :: nil)); auto.
  reflexivity.
Qed.

(* Filter: keep only words of prime length *)

Lemma filter_prime_length_This_is_a_test :
  filter_prime_length_rel
    [ascii_This; ascii_is; ascii_a; ascii_test]
    [ascii_is].
Proof.
  constructor.
  - (* ascii_This length = 4, not prime *)
    simpl. intro C. apply not_prime_four; assumption.
  - constructor.
    + (* ascii_is length = 2, prime *)
      simpl. apply prime_two.
    + constructor.
      * (* ascii_a length = 1, not prime *)
        simpl. intro C. apply not_prime_one; assumption.
      * constructor.
        -- (* ascii_test length = 4, not prime *)
           simpl. intro C. apply not_prime_four; assumption.
        -- constructor.
Qed.

(* Join filtered words to form the output string *)

Lemma join_words_is :
  join_words_rel [ascii_is] (list_ascii_of_string "is").
Proof.
  unfold ascii_is.
  simpl.
  constructor.
Qed.

(* Final theorem assembling everything *)

Example test_words_in_sentence_is :
  problem_143_spec "This is a test" "is".
Proof.
  unfold problem_143_spec.
  exists [ascii_This; ascii_is; ascii_a; ascii_test].
  exists [ascii_is].
  repeat split.
  - apply split_words_This_is_a_test.
  - apply filter_prime_length_This_is_a_test.
  - apply join_words_is.
Qed.

Qed.