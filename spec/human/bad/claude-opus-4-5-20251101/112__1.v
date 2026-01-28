Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Bool.Bool.
Import ListNotations.

Inductive exists_in_list {A : Type} : A -> list A -> Prop :=
| eil_head : forall x xs, exists_in_list x (x :: xs)
| eil_tail : forall x y xs, exists_in_list x xs -> exists_in_list x (y :: xs).

Inductive delete_chars_rel : list ascii -> list ascii -> list ascii -> Prop :=
| dcr_nil : forall c, delete_chars_rel nil c nil
| dcr_delete : forall h t c res, exists_in_list h c ->
    delete_chars_rel t c res ->
    delete_chars_rel (h :: t) c res
| dcr_keep : forall h t c res, ~ exists_in_list h c ->
    delete_chars_rel t c res ->
    delete_chars_rel (h :: t) c (h :: res).

Inductive is_pal_rel : list ascii -> Prop :=
| ipr_nil : is_pal_rel nil
| ipr_single : forall c, is_pal_rel [c]
| ipr_pair : forall c s, is_pal_rel s -> is_pal_rel (c :: (s ++ [c])).

Definition problem_112_pre (s c : string) : Prop :=
  let ls := list_ascii_of_string s in
  let lc := list_ascii_of_string c in
  Forall (fun ch => let n := nat_of_ascii ch in 97 <= n /\ n <= 122) ls /\
  Forall (fun ch => let n := nat_of_ascii ch in 97 <= n /\ n <= 122) lc.

Definition problem_112_spec (s c : string) (output : string * bool) : Prop :=
  let '(res, is_pal) := output in
  let ls := list_ascii_of_string s in
  let lc := list_ascii_of_string c in
  let lres := list_ascii_of_string res in
  delete_chars_rel ls lc lres /\
  (is_pal = true <-> is_pal_rel lres).

(* Define ascii characters we need *)
Definition char_a := "a"%char.
Definition char_b := "b"%char.
Definition char_c := "c"%char.
Definition char_d := "d"%char.
Definition char_e := "e"%char.

(* Lemmas about character membership *)
Lemma a_in_ae : exists_in_list char_a [char_a; char_e].
Proof. apply eil_head. Qed.

Lemma e_in_ae : exists_in_list char_e [char_a; char_e].
Proof. apply eil_tail. apply eil_head. Qed.

Lemma ascii_eq_dec : forall (a b : ascii), {a = b} + {a <> b}.
Proof.
  intros. destruct a, b.
  destruct b, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14;
  try (left; reflexivity); try (right; intro H; inversion H).
Qed.

Lemma b_not_in_ae : ~ exists_in_list char_b [char_a; char_e].
Proof.
  unfold not. intro H.
  inversion H; subst.
  - unfold char_b, char_a in H1. discriminate H1.
  - inversion H2; subst.
    + unfold char_b, char_e in H1. discriminate H1.
    + inversion H3.
Qed.

Lemma c_not_in_ae : ~ exists_in_list char_c [char_a; char_e].
Proof.
  unfold not. intro H.
  inversion H; subst.
  - unfold char_c, char_a in H1. discriminate H1.
  - inversion H2; subst.
    + unfold char_c, char_e in H1. discriminate H1.
    + inversion H3.
Qed.

Lemma d_not_in_ae : ~ exists_in_list char_d [char_a; char_e].
Proof.
  unfold not. intro H.
  inversion H; subst.
  - unfold char_d, char_a in H1. discriminate H1.
  - inversion H2; subst.
    + unfold char_d, char_e in H1. discriminate H1.
    + inversion H3.
Qed.

(* Lemma: "bcd" is not a palindrome *)
Lemma bcd_not_palindrome : ~ is_pal_rel [char_b; char_c; char_d].
Proof.
  unfold not. intro H.
  inversion H; subst.
  - (* ipr_single case impossible *)
    discriminate H1.
  - (* ipr_pair case: c0 :: s ++ [c0] = [char_b; char_c; char_d] *)
    destruct s as [|x xs].
    + simpl in H1. inversion H1. 
      unfold char_b, char_d in H4. discriminate H4.
    + simpl in H1. inversion H1; subst.
      destruct xs as [|y ys].
      * simpl in H4. inversion H4.
        unfold char_b, char_d in H2. discriminate H2.
      * simpl in H4. inversion H4; subst.
        destruct ys as [|z zs].
        -- simpl in H5. discriminate H5.
        -- simpl in H5. discriminate H5.
Qed.

Example test_problem_112 :
  problem_112_spec "abcde" "ae" ("bcd", false).
Proof.
  unfold problem_112_spec.
  simpl.
  split.
  - (* Prove delete_chars_rel *)
    apply dcr_delete.
    + exact a_in_ae.
    + apply dcr_keep.
      * exact b_not_in_ae.
      * apply dcr_keep.
        -- exact c_not_in_ae.
        -- apply dcr_keep.
           ++ exact d_not_in_ae.
           ++ apply dcr_delete.
              ** exact e_in_ae.
              ** apply dcr_nil.
  - (* Prove is_pal = true <-> is_pal_rel lres *)
    split.
    + intro H. discriminate H.
    + intro H. exfalso. apply bcd_not_palindrome. exact H.
Qed.