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

Definition input_str := "go for it".
Definition output_str := "go for it".
Definition w1 := "go".
Definition w2 := "for".
Definition w3 := "it".

(* Axioms to model the behavior of the parameters for this specific test case *)
Axiom split_input : split_by_space input_str = [w1; w2; w3].
Axiom len_w1 : word_length w1 = 2.
Axiom len_w2 : word_length w2 = 3.
Axiom len_w3 : word_length w3 = 2.
Axiom join_output : join_by_space [w1; w2; w3] = output_str.

(* --- Helper Lemmas --- *)

Lemma prime_2 : is_prime 2.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hge2 Hsq.
    assert (H: 2 * 2 <= d * d).
    { apply Nat.mul_le_mono; assumption. }
    lia.
Qed.

Lemma prime_3 : is_prime 3.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hge2 Hsq.
    assert (H: 2 * 2 <= d * d).
    { apply Nat.mul_le_mono; assumption. }
    lia.
Qed.

(* --- Main Proof --- *)

Example test_prime_words : words_in_sentence_spec input_str output_str.
Proof.
  unfold words_in_sentence_spec.
  rewrite split_input.
  
  (* Since all words have prime lengths, the filtered list is the same as the input list *)
  exists [w1; w2; w3].
  
  split.
  
  (* 1. Prove In w filtered <-> In w words /\ is_prime (len w) *)
  - intros w. split.
    + (* -> *)
      intros H_in.
      simpl in H_in. destruct H_in as [H_w1 | [H_w2 | [H_w3 | H_false]]].
      * subst w. split.
        -- simpl. left. reflexivity.
        -- rewrite len_w1. apply prime_2.
      * subst w. split.
        -- simpl. right. left. reflexivity.
        -- rewrite len_w2. apply prime_3.
      * subst w. split.
        -- simpl. right. right. left. reflexivity.
        -- rewrite len_w3. apply prime_2.
      * contradiction.
    + (* <- *)
      intros [H_in H_prime].
      assumption.

  - split.
    (* 2. Prove index preservation *)
    + intros i j wa wb Hi Hj H_lt.
      (* Since filtered list == input list, we can just use i'=i and j'=j *)
      exists i, j.
      split; [assumption | split; [assumption | assumption]].

    (* 3. Prove result string construction *)
    + rewrite join_output. reflexivity.
Qed.