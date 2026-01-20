(* HumanEval 143 - Inductive Spec *)
Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.

Inductive has_divisor_from_rel : nat -> nat -> Prop :=
| hdfr_base : forall n d, n mod d = 0 -> d > 1 -> has_divisor_from_rel n d
| hdfr_step : forall n d, has_divisor_from_rel n (S d) -> has_divisor_from_rel n d.

Inductive is_prime_rel : nat -> Prop :=
| ipr_prime : forall n, n > 1 -> ~ (exists d, 2 <= d <= n - 1 /\ has_divisor_from_rel n d) ->
   is_prime_rel n.

Inductive split_words_rel : list ascii -> list (list ascii) -> Prop :=
| swr_nil : split_words_rel nil nil
| swr_space_skip : forall c cs words, Ascii.eqb c " "%char = true ->
    split_words_rel cs words ->
    split_words_rel (c :: cs) words
| swr_space_finish : forall c cs cur words, Ascii.eqb c " "%char = true ->
    cur <> nil -> split_words_rel cs words ->
    split_words_rel (c :: cs) ((rev cur) :: words)
| swr_char : forall c cs cur words, Ascii.eqb c " "%char = false ->
    split_words_rel cs words ->
    split_words_rel (c :: cs) ((c :: cur) :: words).

Inductive filter_prime_length_rel : list (list ascii) -> list (list ascii) -> Prop :=
| fplr_nil : filter_prime_length_rel nil nil
| fplr_keep : forall w ws res, is_prime_rel (length w) -> filter_prime_length_rel ws res ->
    filter_prime_length_rel (w :: ws) (w :: res)
| fplr_drop : forall w ws res, ~ is_prime_rel (length w) -> filter_prime_length_rel ws res ->
    filter_prime_length_rel (w :: ws) res.

Inductive join_words_rel : list (list ascii) -> list ascii -> Prop :=
| jwr_nil : join_words_rel nil nil
| jwr_single : forall w, join_words_rel (w :: nil) w
| jwr_multi : forall w ws res, join_words_rel ws res ->
    join_words_rel (w :: ws) (w ++ (" "%char :: nil) ++ res).

Definition words_in_sentence_spec (sentence : list ascii) (output : list ascii) : Prop :=
  exists words filtered, split_words_rel sentence words /\
    filter_prime_length_rel words filtered /\
    join_words_rel filtered output.

