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

Definition input_str := "Python programming is fun".
Definition output_str := "programming is fun".
Definition w1 := "Python".
Definition w2 := "programming".
Definition w3 := "is".
Definition w4 := "fun".

(* Axioms to model the behavior of the parameters for this specific test case *)
Axiom split_input : split_by_space input_str = [w1; w2; w3; w4].
Axiom len_w1 : word_length w1 = 6.
Axiom len_w2 : word_length w2 = 11.
Axiom len_w3 : word_length w3 = 2.
Axiom len_w4 : word_length w4 = 3.
Axiom join_output : join_by_space [w2; w3; w4] = output_str.

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

Lemma not_prime_6 : ~ is_prime 6.
Proof.
  unfold is_prime. intros [_ H].
  specialize (H 2).
  assert (2 <= 2) by lia.
  assert (2 * 2 <= 6) by lia.
  apply H in H0; [| assumption].
  simpl in H0. contradiction.
Qed.

Lemma prime_11 : is_prime 11.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hge2 Hsq.
    (* If d >= 4, d*d >= 16 > 11. So d < 4. *)
    assert (d < 4).
    { destruct d. lia. destruct d. lia. destruct d. lia. destruct d. lia.
      simpl in Hsq. lia. }
    assert (d = 2 \/ d = 3) by lia.
    destruct H as [-> | ->].
    + simpl. discriminate.
    + simpl. discriminate.
Qed.

(* --- Main Proof --- *)

Example test_prime_words : words_in_sentence_spec input_str output_str.
Proof.
  unfold words_in_sentence_spec.
  rewrite split_input.
  
  (* We propose that the filtered list is [w2; w3; w4] *)
  exists [w2; w3; w4].
  
  split.
  
  (* 1. Prove In w filtered <-> In w words /\ is_prime (len w) *)
  - intros w. split.
    + (* -> *)
      intros H_in.
      simpl in H_in.
      destruct H_in as [H_w2 | [H_w3 | [H_w4 | H_false]]].
      * subst w. split.
        -- simpl. right. left. reflexivity.
        -- rewrite len_w2. apply prime_11.
      * subst w. split.
        -- simpl. right. right. left. reflexivity.
        -- rewrite len_w3. apply prime_2.
      * subst w. split.
        -- simpl. right. right. right. left. reflexivity.
        -- rewrite len_w4. apply prime_3.
      * contradiction.
    + (* <- *)
      intros [H_in H_prime].
      simpl in H_in.
      destruct H_in as [H_w1 | [H_w2 | [H_w3 | [H_w4 | H_false]]]].
      * (* w = w1 *)
        subst w. rewrite len_w1 in H_prime. apply not_prime_6 in H_prime. contradiction.
      * (* w = w2 *)
        subst w. simpl. left. reflexivity.
      * (* w = w3 *)
        subst w. simpl. right. left. reflexivity.
      * (* w = w4 *)
        subst w. simpl. right. right. left. reflexivity.
      * contradiction.

  - split.
    (* 2. Prove index preservation *)
    + intros i j wa wb Hi Hj H_lt.
      (* filtered_words is [w2; w3; w4] *)
      destruct i.
      * (* i = 0, wa = w2 *)
        simpl in Hi. injection Hi as Hi_eq. subst wa.
        destruct j.
        -- lia.
        -- destruct j.
           ++ (* j = 1, wb = w3 *)
              simpl in Hj. injection Hj as Hj_eq. subst wb.
              (* w2 is at index 1 in words, w3 is at index 2 *)
              exists 1, 2. split; [reflexivity | split; [reflexivity | lia]].
           ++ destruct j.
              ** (* j = 2, wb = w4 *)
                 simpl in Hj. injection Hj as Hj_eq. subst wb.
                 (* w2 is at index 1 in words, w4 is at index 3 *)
                 exists 1, 3. split; [reflexivity | split; [reflexivity | lia]].
              ** simpl in Hj. discriminate.
      * destruct i.
        -- (* i = 1, wa = w3 *)
           simpl in Hi. injection Hi as Hi_eq. subst wa.
           destruct j.
           ++ lia.
           ++ destruct j.
              ** lia.
              ** destruct j.
                 --- (* j = 2, wb = w4 *)
                     simpl in Hj. injection Hj as Hj_eq. subst wb.
                     (* w3 is at index 2 in words, w4 is at index 3 *)
                     exists 2, 3. split; [reflexivity | split; [reflexivity | lia]].
                 --- simpl in Hj. discriminate.
        -- destruct i.
           ++ (* i = 2, wa = w4 *)
              simpl in Hi. injection Hi as Hi_eq. subst wa.
              destruct j; [lia|destruct j; [lia|destruct j; [lia|]]].
              simpl in Hj. discriminate.
           ++ simpl in Hi. discriminate.

    (* 3. Prove result string construction *)
    + rewrite join_output. reflexivity.
Qed.