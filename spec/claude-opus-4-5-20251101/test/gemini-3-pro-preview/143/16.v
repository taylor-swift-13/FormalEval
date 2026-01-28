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

Definition input_str := "I love eating pizza".
Definition output_str := "pizza".
Definition w1 := "I".
Definition w2 := "love".
Definition w3 := "eating".
Definition w4 := "pizza".

(* Axioms to model the behavior of the parameters for this specific test case *)
Axiom split_input : split_by_space input_str = [w1; w2; w3; w4].
Axiom len_w1 : word_length w1 = 1.
Axiom len_w2 : word_length w2 = 4.
Axiom len_w3 : word_length w3 = 6.
Axiom len_w4 : word_length w4 = 5.
Axiom join_output : join_by_space [w4] = output_str.

(* --- Helper Lemmas --- *)

Lemma not_prime_1 : ~ is_prime 1.
Proof.
  unfold is_prime. intros [H _]. lia.
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

Lemma not_prime_6 : ~ is_prime 6.
Proof.
  unfold is_prime. intros [_ H].
  specialize (H 2).
  assert (2 <= 2) by lia.
  assert (2 * 2 <= 6) by lia.
  apply H in H0; [| assumption].
  simpl in H0. contradiction.
Qed.

Lemma prime_5 : is_prime 5.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hge2 Hsq.
    (* If d >= 2 and d*d <= 5, d must be 2 *)
    assert (d = 2).
    {
      destruct d; [lia|].
      destruct d; [lia|].
      destruct d; [reflexivity|].
      simpl in Hsq. lia. 
    }
    subst d. simpl. discriminate.
Qed.

(* --- Main Proof --- *)

Example test_prime_words : words_in_sentence_spec input_str output_str.
Proof.
  unfold words_in_sentence_spec.
  rewrite split_input.
  
  (* We propose that the filtered list is just ["pizza"] *)
  exists [w4].
  
  split.
  
  (* 1. Prove In w filtered <-> In w words /\ is_prime (len w) *)
  - intros w. split.
    + (* -> *)
      intros H_in.
      simpl in H_in. destruct H_in as [H_eq | H_false].
      * subst w. split.
        -- simpl. right. right. right. left. reflexivity.
        -- rewrite len_w4. apply prime_5.
      * contradiction.
    + (* <- *)
      intros [H_in H_prime].
      simpl in H_in.
      destruct H_in as [H_w1 | [H_w2 | [H_w3 | [H_w4 | H_false]]]].
      * (* w = "I" *)
        subst w. rewrite len_w1 in H_prime. apply not_prime_1 in H_prime. contradiction.
      * (* w = "love" *)
        subst w. rewrite len_w2 in H_prime. apply not_prime_4 in H_prime. contradiction.
      * (* w = "eating" *)
        subst w. rewrite len_w3 in H_prime. apply not_prime_6 in H_prime. contradiction.
      * (* w = "pizza" *)
        subst w. simpl. left. reflexivity.
      * contradiction.

  - split.
    (* 2. Prove index preservation *)
    + intros i j wa wb Hi Hj H_lt.
      (* filtered_words is [w4], so length is 1. Valid indices are only 0. *)
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