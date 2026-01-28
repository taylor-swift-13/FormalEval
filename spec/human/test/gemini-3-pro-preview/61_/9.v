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

Example test_case_1 : problem_61_spec [")"%char] false.
Proof.
  unfold problem_61_spec.
  split.
  - intros H. discriminate.
  - intros H.
    assert (forall l, is_correctly_bracketed l -> l <> [] -> exists t, l = "("%char :: t) as StartOpen.
    {
      clear H. intros l Hbrack. induction Hbrack as [| l' H' IH | l1 l2 H1 IH1 H2 IH2].
      - intros Hneq. contradiction.
      - intros _. exists (l' ++ [")"%char]). reflexivity.
      - intros Hneq. destruct l1.
        + simpl in *. apply IH2. assumption.
        + assert (a :: l1 <> []) by discriminate.
          apply IH1 in H. destruct H as [t Ht].
          rewrite Ht. exists (t ++ l2). reflexivity.
    }
    apply StartOpen in H.
    + destruct H as [t Ht]. discriminate Ht.
    + discriminate.
Qed.