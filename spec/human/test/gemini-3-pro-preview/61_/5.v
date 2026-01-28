Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii Coq.Strings.String.
Import ListNotations.

Inductive is_correctly_bracketed : list ascii -> Prop :=
  | cb_nil    : is_correctly_bracketed []
  | cb_nest   : forall l,
                  is_correctly_bracketed l ->
                  is_correctly_bracketed ("("%char :: l ++ [")"%char])
  | cb_concat : forall l1 l2,
                  is_correctly_bracketed l1 ->
                  is_correctly_bracketed l2 ->
                  is_correctly_bracketed (l1 ++ l2).

Definition problem_61_pre (brackets : string) : Prop :=
  Forall (fun c => c = "("%char \/ c = ")"%char) (list_ascii_of_string brackets).

Definition problem_61_spec (brackets : list ascii) (b : bool) : Prop :=
  b = true <-> is_correctly_bracketed brackets.

Lemma cb_count_eq : forall l, is_correctly_bracketed l -> 
  count_occ ascii_dec l "("%char = count_occ ascii_dec l ")"%char.
Proof.
  intros l H. induction H.
  - reflexivity.
  - simpl. rewrite !count_occ_app. simpl.
    destruct (ascii_dec "("%char "("%char); [|contradiction].
    destruct (ascii_dec ")"%char "("%char); [discriminate|].
    destruct (ascii_dec "("%char ")"%char); [discriminate|].
    destruct (ascii_dec ")"%char ")"%char); [|contradiction].
    rewrite IHis_correctly_bracketed.
    rewrite <- plus_n_Sm. rewrite <- plus_n_O. reflexivity.
  - rewrite !count_occ_app. rewrite IHis_correctly_bracketed1, IHis_correctly_bracketed2. reflexivity.
Qed.

Example test_case_1 : problem_61_spec (list_ascii_of_string "((()())))") false.
Proof.
  unfold problem_61_spec.
  split.
  - intros H. inversion H.
  - intros H.
    apply cb_count_eq in H.
    simpl in H.
    discriminate H.
Qed.