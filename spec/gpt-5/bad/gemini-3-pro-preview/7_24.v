Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

Definition contains_substring (substring s : string) : Prop :=
  exists pre post, s = String.append pre (String.append substring post).

Inductive filtered (P : string -> Prop) : list string -> list string -> Prop :=
| filtered_nil : filtered P [] []
| filtered_cons_true : forall x l l', P x -> filtered P l l' -> filtered P (x :: l) (x :: l')
| filtered_cons_false : forall x l l', ~ P x -> filtered P l l' -> filtered P (x :: l) l'.

Definition filter_by_substring_spec (strings : list string) (substring : string) (res : list string) : Prop :=
  filtered (contains_substring substring) strings res.

Lemma string_length_append : forall s1 s2, String.length (s1 ++ s2) = String.length s1 + String.length s2.
Proof.
  induction s1; simpl; intros; auto.
  f_equal; auto.
Qed.

Lemma contains_substring_length_bound : forall sub s, contains_substring sub s -> String.length sub <= String.length s.
Proof.
  intros sub s [pre [post H]].
  rewrite H.
  repeat rewrite string_length_append.
  auto with arith.
Qed.

Example test_case : filter_by_substring_spec ["earth"; "mars"; "jupiter"; "saturn"; "uranus"] "numpuranusys" [].
Proof.
  unfold filter_by_substring_spec.
  apply filtered_cons_false.
  - intro H. apply contains_substring_length_bound in H. simpl in H. inversion H.
  - apply filtered_cons_false.
    + intro H. apply contains_substring_length_bound in H. simpl in H. inversion H.
    + apply filtered_cons_false.
      * intro H. apply contains_substring_length_bound in H. simpl in H. inversion H.
      * apply filtered_cons_false.
        -- intro H. apply contains_substring_length_bound in H. simpl in H. inversion H.
        -- apply filtered_cons_false.
           ++ intro H. apply contains_substring_length_bound in H. simpl in H. inversion H.
           ++ apply filtered_nil.
Qed.