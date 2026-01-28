Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.Arith Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.

(* --- Specification Definitions (Provided) --- *)

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
    split_words_aux_rel (" " :: cs) nil words_rev
| swar_space_finish : forall cs cur words_rev,
    cur <> nil ->
    split_words_aux_rel cs nil words_rev ->
    split_words_aux_rel (" " :: cs) cur ((rev cur) :: words_rev)
| swar_char : forall c cs cur words_rev,
    Ascii.eqb c " " = false ->
    split_words_aux_rel cs (c :: cur) words_rev ->
    split_words_aux_rel (c :: cs) cur words_rev.

Inductive split_words_rel : list ascii -> list (list ascii) -> Prop :=
| swr_build : forall s words_rev words,
    split_words_aux_rel s nil words_rev ->
    words = rev words_rev ->
    split_words_rel s words.

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
    join_words_rel (w :: ws) (w ++ (" " :: nil) ++ res).

Definition problem_143_pre (sentence : string) : Prop :=
  let l := list_ascii_of_string sentence in
  1 <= length l /\ length l <= 100 /\
  Forall (fun c =>
    let n := nat_of_ascii c in c = " " \/ (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122)) l.

Definition problem_143_spec (sentence : string) (output : string) : Prop :=
  exists words filtered, split_words_rel (list_ascii_of_string sentence) words /\
    filter_prime_length_rel words filtered /\
    join_words_rel filtered (list_ascii_of_string output).

(* --- Proof for Example 1 --- *)

(* Helper lemmas for primality *)

Lemma is_prime_2 : is_prime_rel 2.
Proof.
  constructor.
  - lia.
  - intros [d [Hrange _]]. lia.
Qed.

Lemma not_prime_1 : ~ is_prime_rel 1.
Proof.
  intro H. inversion H. lia.
Qed.

Lemma not_prime_4 : ~ is_prime_rel 4.
Proof.
  intro H. inversion H as [Hgt Hneg]. apply Hneg.
  exists 2. split.
  - lia.
  - apply hdfr_base.
    + reflexivity.
    + lia.
Qed.

(* Tactic to automate the splitting process *)
Ltac solve_split :=
  repeat (
    match goal with
    | [ |- split_words_aux_rel nil _ _ ] => 
        (apply swar_nil_word; [ discriminate ]) || apply swar_nil_empty
    | [ |- split_words_aux_rel (" " :: _) _ _ ] =>
        (apply swar_space_finish; [ discriminate | ]) || apply swar_space_skip
    | [ |- split_words_aux_rel (_ :: _) _ _ ] =>
        apply swar_char; [ reflexivity | ]
    end).

Example test_problem_143 : problem_143_spec "This is a test" "is".
Proof.
  unfold problem_143_spec.
  
  (* Define the words explicitly as list of characters *)
  let w_This := list_ascii_of_string "This" in
  let w_is   := list_ascii_of_string "is" in
  let w_a    := list_ascii_of_string "a" in
  let w_test := list_ascii_of_string "test" in
  
  (* Provide witnesses for the existential quantifiers *)
  exists [w_This; w_is; w_a; w_test].
  exists [w_is].
  
  repeat split.
  
  (* 1. Prove splitting *)
  - eapply swr_build.
    + simpl. solve_split.
    + simpl. reflexivity.

  (* 2. Prove filtering *)
  - (* "This" length 4 -> Drop *)
    apply fplr_drop.
    { simpl. apply not_prime_4. }
    
    (* "is" length 2 -> Keep *)
    apply fplr_keep.
    { simpl. apply is_prime_2. }
    
    (* "a" length 1 -> Drop *)
    apply fplr_drop.
    { simpl. apply not_prime_1. }
      
    (* "test" length 4 -> Drop *)
    apply fplr_drop.
    { simpl. apply not_prime_4. }
      
    (* End of list *)
    apply fplr_nil.

  (* 3. Prove joining *)
  - (* Join ["is"] -> "is" *)
    apply jwr_single.
Qed.