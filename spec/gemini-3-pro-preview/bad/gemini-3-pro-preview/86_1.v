Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Require Import Lia.

Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.

(* Auxiliary function to convert string to list of ascii *)
Definition list_of_string (s : string) : list ascii :=
  list_ascii_of_string s.

(* Definition of ASCII ordering *)
Definition ascii_le (c1 c2 : ascii) : Prop :=
  (nat_of_ascii c1 <= nat_of_ascii c2)%nat.

(* Predicate for a sorted string *)
Definition is_sorted_string (s : string) : Prop :=
  Sorted ascii_le (list_of_string s).

(* Predicate for string permutation (same characters) *)
Definition is_permutation_string (s1 s2 : string) : Prop :=
  Permutation (list_of_string s1) (list_of_string s2).

(* Predicate to ensure a word does not contain spaces (simulating split behavior) *)
(* Note: " "%char specifies the space character *)
Definition word_has_no_space (s : string) : Prop :=
  forall c, In c (list_of_string s) -> c <> " "%char.

(* Function to join a list of strings with spaces *)
Fixpoint join_space (l : list string) : string :=
  match l with
  | [] => ""
  | [s] => s
  | s :: xs => s ++ " " ++ (join_space xs)
  end.

(* Relation defining the transformation of a single word *)
Definition word_transform (input_word output_word : string) : Prop :=
  is_permutation_string input_word output_word /\
  is_sorted_string output_word.

(* Main Specification *)
Definition anti_shuffle_spec (s : string) (result : string) : Prop :=
  exists (words : list string) (ordered_words : list string),
    (* The input string is composed of words separated by spaces *)
    s = join_space words /\
    (* These words are obtained by splitting by space (contain no spaces themselves) *)
    Forall word_has_no_space words /\
    (* The result string is composed of the transformed words joined by spaces *)
    result = join_space ordered_words /\
    (* There is a one-to-one correspondence between input words and output words *)
    Forall2 word_transform words ordered_words.

Example test_hi : anti_shuffle_spec "Hi" "Hi".
Proof.
  unfold anti_shuffle_spec.
  (* Provide the witness lists *)
  exists ["Hi"], ["Hi"].
  (* Prove the conjunctions one by one *)
  split.
  - (* s = join_space words *)
    simpl. reflexivity.
  - split.
    + (* Forall word_has_no_space words *)
      constructor.
      * (* word_has_no_space "Hi" *)
        unfold word_has_no_space.
        simpl.
        intros c H.
        destruct H as [H | [H | H]].
        -- (* c = 'H' *)
           subst. intro Contra. inversion Contra.
        -- (* c = 'i' *)
           subst. intro Contra. inversion Contra.
        -- (* False *)
           contradiction.
      * (* Forall nil *)
        constructor.
    + split.
      * (* result = join_space ordered_words *)
        simpl. reflexivity.
      * (* Forall2 word_transform words ordered_words *)
        constructor.
        -- (* word_transform "Hi" "Hi" *)
           unfold word_transform.
           split.
           ++ (* is_permutation_string "Hi" "Hi" *)
              unfold is_permutation_string.
              apply Permutation_refl.
           ++ (* is_sorted_string "Hi" *)
              unfold is_sorted_string.
              simpl.
              apply Sorted_cons.
              ** (* Sorted tail "i" *)
                 apply Sorted_cons.
                 --- apply Sorted_nil.
                 --- apply HdRel_nil.
              ** (* HdRel ascii_le 'H' 'i' *)
                 apply HdRel_cons.
                 unfold ascii_le.
                 simpl.
                 (* 'H' is 72, 'i' is 105. 72 <= 105 *)
                 lia.
        -- (* Forall2 nil nil *)
           constructor.
Qed.