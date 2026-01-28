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

Example test_case_1 : problem_61_spec [")"%char; ")"%char; "("%char] false.
Proof.
  unfold problem_61_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    assert (H_starts_open : forall l, is_correctly_bracketed l -> l <> [] -> exists tl, l = "("%char :: tl).
    {
      intros l H_cb. induction H_cb.
      - intros H_neq. contradiction.
      - intros _. exists (l ++ [")"%char]). reflexivity.
      - intros H_neq.
        destruct l1 as [| c l1'].
        + simpl in *. apply IHHcb2. assumption.
        + assert (H_nn : c :: l1' <> []) by discriminate.
          apply IHHcb1 in H_nn.
          destruct H_nn as [tl H_eq].
          rewrite H_eq.
          exists (tl ++ l2). reflexivity.
    }
    apply H_starts_open in H.
    + destruct H as [tl H_eq].
      inversion H_eq.
    + discriminate.
Qed.