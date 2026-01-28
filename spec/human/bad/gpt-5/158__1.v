Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.

Inductive string_le_rel : string -> string -> Prop :=
| slr_empty : forall s, string_le_rel EmptyString s
| slr_lt : forall c1 s1 c2 s2,
    nat_of_ascii c1 < nat_of_ascii c2 ->
    string_le_rel (String c1 s1) (String c2 s2)
| slr_eq : forall c s1 s2,
    string_le_rel s1 s2 ->
    string_le_rel (String c s1) (String c s2).

Inductive string_contains_rel (c : ascii) : string -> Prop :=
| scr_head : forall s, string_contains_rel c (String c s)
| scr_tail : forall x s, string_contains_rel c s -> string_contains_rel c (String x s).

Inductive count_unique_chars_rel : string -> nat -> Prop :=
| cucr_empty : count_unique_chars_rel EmptyString 0
| cucr_seen : forall c s n,
    string_contains_rel c s ->
    count_unique_chars_rel s n ->
    count_unique_chars_rel (String c s) n
| cucr_new : forall c s n,
    ~ string_contains_rel c s ->
    count_unique_chars_rel s n ->
    count_unique_chars_rel (String c s) (S n).

Definition problem_158_pre (words : list string) : Prop := words <> [].

Definition problem_158_spec (words : list string) (result : string) : Prop :=
  In result words /\
  forall w, In w words ->
    exists c_res c_w,
      count_unique_chars_rel result c_res /\
      count_unique_chars_rel w c_w /\
      (c_res > c_w \/ (c_res = c_w /\ string_le_rel result w)).

Lemma contains_inv :
  forall c x s,
    string_contains_rel c (String x s) ->
    x = c \/ string_contains_rel c s.
Proof.
  intros c x s H. inversion H; subst; auto.
Qed.

Lemma no_contains_empty : forall c, ~ string_contains_rel c EmptyString.
Proof.
  intros c H. inversion H.
Qed.

(* Specific non-containment lemmas for "string" *)
Lemma not_contains_s_tring : ~ string_contains_rel "115"%char "tring".
Proof.
  intros H.
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply no_contains_empty in H. contradiction.
Qed.

Lemma not_contains_t_ring : ~ string_contains_rel "116"%char "ring".
Proof.
  intros H.
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply no_contains_empty in H. contradiction.
Qed.

Lemma not_contains_r_ing : ~ string_contains_rel "114"%char "ing".
Proof.
  intros H.
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply no_contains_empty in H. contradiction.
Qed.

Lemma not_contains_i_ng : ~ string_contains_rel "105"%char "ng".
Proof.
  intros H.
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply no_contains_empty in H. contradiction.
Qed.

Lemma not_contains_n_g : ~ string_contains_rel "110"%char "g".
Proof.
  intros H.
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply no_contains_empty in H. contradiction.
Qed.

(* Specific non-containment lemmas for "name" *)
Lemma not_contains_e_empty : ~ string_contains_rel "101"%char EmptyString.
Proof. apply no_contains_empty. Qed.

Lemma not_contains_m_e : ~ string_contains_rel "109"%char "e".
Proof.
  intros H.
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply no_contains_empty in H. contradiction.
Qed.

Lemma not_contains_a_me : ~ string_contains_rel "097"%char "me".
Proof.
  intros H.
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply no_contains_empty in H. contradiction.
Qed.

Lemma not_contains_n_ame : ~ string_contains_rel "110"%char "ame".
Proof.
  intros H.
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply no_contains_empty in H. contradiction.
Qed.

(* Specific non-containment lemmas for "of" *)
Lemma not_contains_f_empty : ~ string_contains_rel "102"%char EmptyString.
Proof. apply no_contains_empty. Qed.

Lemma not_contains_o_f : ~ string_contains_rel "111"%char "f".
Proof.
  intros H.
  apply contains_inv in H. destruct H as [Heq|H]; [discriminate Heq|].
  apply no_contains_empty in H. contradiction.
Qed.

(* Count lemmas *)
Lemma count_string_6 : count_unique_chars_rel "string" 6.
Proof.
  assert (H0 : count_unique_chars_rel EmptyString 0) by constructor.
  assert (Hg1 : count_unique_chars_rel "g" 1).
  { apply cucr_new; [apply no_contains_empty| exact H0]. }
  assert (Hng2 : count_unique_chars_rel "ng" 2).
  { apply cucr_new; [apply not_contains_n_g| exact Hg1]. }
  assert (Hing3 : count_unique_chars_rel "ing" 3).
  { apply cucr_new; [apply not_contains_i_ng| exact Hng2]. }
  assert (Hring4 : count_unique_chars_rel "ring" 4).
  { apply cucr_new; [apply not_contains_r_ing| exact Hing3]. }
  assert (Htring5 : count_unique_chars_rel "tring" 5).
  { apply cucr_new; [apply not_contains_t_ring| exact Hring4]. }
  apply cucr_new; [apply not_contains_s_tring| exact Htring5].
Qed.

Lemma count_name_4 : count_unique_chars_rel "name" 4.
Proof.
  assert (H0 : count_unique_chars_rel EmptyString 0) by constructor.
  assert (He1 : count_unique_chars_rel "e" 1).
  { apply cucr_new; [apply not_contains_e_empty| exact H0]. }
  assert (Hme2 : count_unique_chars_rel "me" 2).
  { apply cucr_new; [apply not_contains_m_e| exact He1]. }
  assert (Hame3 : count_unique_chars_rel "ame" 3).
  { apply cucr_new; [apply not_contains_a_me| exact Hme2]. }
  apply cucr_new; [apply not_contains_n_ame| exact Hame3].
Qed.

Lemma count_of_2 : count_unique_chars_rel "of" 2.
Proof.
  assert (H0 : count_unique_chars_rel EmptyString 0) by constructor.
  assert (Hf1 : count_unique_chars_rel "f" 1).
  { apply cucr_new; [apply not_contains_f_empty| exact H0]. }
  apply cucr_new; [apply not_contains_o_f| exact Hf1].
Qed.

(* Reflexivity of lexicographical order *)
Lemma string_le_refl : forall s, string_le_rel s s.
Proof.
  induction s as [| c s' IH]; simpl.
  - apply slr_empty.
  - apply slr_eq. exact IH.
Qed.

Example problem_158_testcase_1 :
  problem_158_spec ["name"; "of"; "string"] "string".
Proof.
  split.
  - simpl. right. right. left. reflexivity.
  - intros w Hin.
    assert (Cstring : count_unique_chars_rel "string" 6) by apply count_string_6.
    simpl in Hin. destruct Hin as [Hw|[Hw|Hw]].
    + subst w.
      exists 6, 4.
      split; [assumption|].
      split; [apply count_name_4|].
      left. lia.
    + subst w.
      exists 6, 2.
      split; [assumption|].
      split; [apply count_of_2|].
      left. lia.
    + subst w.
      exists 6, 6.
      split; [assumption|].
      split; [assumption|].
      right. split; [reflexivity|].
      apply string_le_refl.
Qed.