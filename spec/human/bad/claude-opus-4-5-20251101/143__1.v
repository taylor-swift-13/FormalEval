Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.

Inductive has_divisor_from_rel : nat -> nat -> Prop :=
| hdfr_base : forall n d, n mod d = 0 -> d > 1 -> has_divisor_from_rel n d
| hdfr_step : forall n d, has_divisor_from_rel n (S d) -> has_divisor_from_rel n d.

Inductive is_prime_rel : nat -> Prop :=
| ipr_prime : forall n, n > 1 -> ~ (exists d, 2 <= d <= n - 1 /\ has_divisor_from_rel n d) ->
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
| fplr_keep : forall (w : list ascii) (ws res : list (list ascii)), 
    is_prime_rel (List.length w) -> filter_prime_length_rel ws res ->
    filter_prime_length_rel (w :: ws) (w :: res)
| fplr_drop : forall (w : list ascii) (ws res : list (list ascii)), 
    ~ is_prime_rel (List.length w) -> filter_prime_length_rel ws res ->
    filter_prime_length_rel (w :: ws) res.

Inductive join_words_rel : list (list ascii) -> list ascii -> Prop :=
| jwr_nil : join_words_rel nil nil
| jwr_single : forall w, join_words_rel (w :: nil) w
| jwr_multi : forall w ws res, ws <> nil -> join_words_rel ws res ->
    join_words_rel (w :: ws) (w ++ (" "%char :: nil) ++ res).

Definition problem_143_pre (sentence : string) : Prop :=
  let l := list_ascii_of_string sentence in
  1 <= List.length l /\ List.length l <= 100 /\
  Forall (fun c =>
    let n := nat_of_ascii c in c = " "%char \/ (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122)) l.

Definition problem_143_spec (sentence : string) (output : string) : Prop :=
  exists words filtered, split_words_rel (list_ascii_of_string sentence) words /\
    filter_prime_length_rel words filtered /\
    join_words_rel filtered (list_ascii_of_string output).

Lemma two_is_prime : is_prime_rel 2.
Proof.
  apply ipr_prime.
  - lia.
  - intros [d [Hle Hdiv]]. lia.
Qed.

Lemma four_not_prime : ~ is_prime_rel 4.
Proof.
  intros H.
  inversion H; subst.
  apply H1.
  exists 2.
  split.
  - lia.
  - apply hdfr_base; lia.
Qed.

Lemma one_not_prime : ~ is_prime_rel 1.
Proof.
  intros H.
  inversion H; subst.
  lia.
Qed.

Example problem_143_test1 : problem_143_spec "This is a test" "is".
Proof.
  unfold problem_143_spec.
  exists [["T"%char; "h"%char; "i"%char; "s"%char];
          ["i"%char; "s"%char];
          ["a"%char];
          ["t"%char; "e"%char; "s"%char; "t"%char]].
  exists [["i"%char; "s"%char]].
  split.
  - apply swr_build with (words_rev := 
      [["t"%char; "e"%char; "s"%char; "t"%char];
       ["a"%char];
       ["i"%char; "s"%char];
       ["T"%char; "h"%char; "i"%char; "s"%char]]).
    + simpl.
      apply swar_char. reflexivity.
      apply swar_char. reflexivity.
      apply swar_char. reflexivity.
      apply swar_char. reflexivity.
      apply swar_space_finish.
      * discriminate.
      * apply swar_char. reflexivity.
        apply swar_char. reflexivity.
        apply swar_space_finish.
        -- discriminate.
        -- apply swar_char. reflexivity.
           apply swar_space_finish.
           ++ discriminate.
           ++ apply swar_char. reflexivity.
              apply swar_char. reflexivity.
              apply swar_char. reflexivity.
              apply swar_char. reflexivity.
              apply swar_nil_word.
              discriminate.
    + reflexivity.
  - split.
    + simpl.
      apply fplr_drop.
      * exact four_not_prime.
      * apply fplr_keep.
        -- exact two_is_prime.
        -- apply fplr_drop.
           ++ exact one_not_prime.
           ++ apply fplr_drop.
              ** exact four_not_prime.
              ** apply fplr_nil.
    + simpl.
      apply jwr_single.
Qed.