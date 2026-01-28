Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope string_scope.

(* --- Specification Definition --- *)

Definition is_prime (n : nat) : Prop :=
  n >= 2 /\ forall d : nat, 2 <= d -> d * d <= n -> ~ (Nat.modulo n d = 0).

Definition word := string.

Parameter split_by_space : string -> list word.
Parameter join_by_space : list word -> string.
Parameter word_length : word -> nat.

Definition words_in_sentence_spec (sentence : string) (result : string) : Prop :=
  let words := split_by_space sentence in
  (* The specification implies filtering logic, captured by the exists clause *)
  exists filtered_words : list word,
    (forall w, In w filtered_words <-> (In w words /\ is_prime (word_length w))) /\
    (forall i j w1 w2, 
      nth_error filtered_words i = Some w1 ->
      nth_error filtered_words j = Some w2 ->
      i < j ->
      exists i' j', 
        nth_error words i' = Some w1 /\
        nth_error words j' = Some w2 /\
        i' < j') /\
    result = join_by_space filtered_words.

(* --- Test Case Setup --- *)

Definition input_str := "here is".
Definition output_str := "is".
Definition w1 := "here".
Definition w2 := "is".

(* Axioms to model the behavior of the parameters for this specific test case *)
Axiom split_input : split_by_space input_str = [w1; w2].
Axiom len_w1 : word_length w1 = 4.
Axiom len_w2 : word_length w2 = 2.
Axiom join_output : join_by_space [w2] = output_str.

(* --- Helper Lemmas --- *)

Lemma prime_2 : is_prime 2.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hge2 Hsq.
    (* If d >= 2, then d * d >= 4. But we have d * d <= 2. Contradiction. *)
    assert (H: 2 * 2 <= d * d).
    { apply Nat.mul_le_mono; assumption. }
    lia.
Qed.

Lemma not_prime_4 : ~ is_prime 4.
Proof.
  unfold is_prime. intros [_ H].
  specialize (H 2).
  assert (2 <= 2) by lia.
  assert (2 * 2 <= 4) by lia.
  apply H in H0; [| assumption].
  simpl in H0. contradiction.
Qed.

(* --- Main Proof --- *)

Example test_prime_words : words_in_sentence_spec input_str output_str.
Proof.
  unfold words_in_sentence_spec.
  rewrite split_input.
  
  (* We propose that the filtered list is just ["is"] *)
  exists [w2].
  
  split.
  
  (* 1. Prove In w filtered <-> In w words /\ is_prime (len w) *)
  - intros w. split.
    + (* -> *)
      intros H_in.
      simpl in H_in. destruct H_in as [H_eq | H_false].
      * subst w. split.
        -- simpl. right. left. reflexivity.
        -- rewrite len_w2. apply prime_2.
      * contradiction.
    + (* <- *)
      intros [H_in H_prime].
      simpl in H_in.
      destruct H_in as [H_w1 | [H_w2 | H_false]].
      * (* w = "here" *)
        subst w. rewrite len_w1 in H_prime. apply not_prime_4 in H_prime. contradiction.
      * (* w = "is" *)
        subst w. simpl. left. reflexivity.
      * contradiction.

  - split.
    (* 2. Prove index preservation *)
    + intros i j wa wb Hi Hj H_lt.
      (* filtered_words is [w2], so length is 1. Valid indices are only 0. *)
      destruct i.
      * (* i = 0 *)
        simpl in Hi. injection Hi as Hi_eq. subst wa.
        destruct j.
        -- (* j = 0 *) lia. (* i < j -> 0 < 0 contradiction *)
        -- (* j > 0 *)
           destruct j; simpl in Hj; discriminate.
      * (* i > 0 *)
        destruct i; simpl in Hi; discriminate.

    (* 3. Prove result string construction *)
    + rewrite join_output. reflexivity.
Qed.