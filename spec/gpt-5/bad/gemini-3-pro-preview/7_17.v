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
  induction s1; simpl; intros.
  - reflexivity.
  - rewrite IHs1. reflexivity.
Qed.

Lemma not_contains_if_len_lt : forall sub s, String.length s < String.length sub -> ~ contains_substring sub s.
Proof.
  intros sub s Hlen [pre [post H]].
  apply (f_equal String.length) in H.
  rewrite string_length_append in H.
  rewrite string_length_append in H.
  assert (String.length sub <= String.length s).
  { rewrite H. rewrite <- Nat.add_assoc. apply Nat.le_add_r. }
  apply Nat.lt_not_le in Hlen. contradiction.
Qed.

Example test_case : filter_by_substring_spec ["hello"; "world"; "python"; "numpy"; "pandas"] "antidisestablishmentarianismpy" [].
Proof.
  unfold filter_by_substring_spec.
  apply filtered_cons_false. { apply not_contains_if_len_lt; simpl; repeat constructor. }
  apply filtered_cons_false. { apply not_contains_if_len_lt; simpl; repeat constructor. }
  apply filtered_cons_false. { apply not_contains_if_len_lt; simpl; repeat constructor. }
  apply filtered_cons_false. { apply not_contains_if_len_lt; simpl; repeat constructor. }
  apply filtered_cons_false. { apply not_contains_if_len_lt; simpl; repeat constructor. }
  apply filtered_nil.
Qed.