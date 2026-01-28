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

Lemma cb_starts_with_open : forall l,
  is_correctly_bracketed l ->
  l <> [] ->
  exists l', l = "("%char :: l'.
Proof.
  intros l H. induction H.
  - intros Hcontra. contradiction.
  - intros _. exists (l ++ [")"%char]). reflexivity.
  - intros Hneq. destruct l1 as [|c l1'].
    + simpl in *. apply IHis_correctly_bracketed2. apply Hneq.
    + assert (Hnn: c :: l1' <> []). { discriminate. }
      apply IHis_correctly_bracketed1 in Hnn.
      destruct Hnn as [tl Heq].
      rewrite Heq. simpl. exists (tl ++ l2). reflexivity.
Qed.

Example test_case_2 : problem_61_spec [")"%char; "("%char; ")"%char; "("%char; ")"%char; ")"%char; ")"%char; "("%char] false.
Proof.
  unfold problem_61_spec.
  split.
  - intros H. discriminate.
  - intros H.
    apply cb_starts_with_open in H.
    + destruct H as [l' H]. inversion H.
    + unfold not. intro Hcontra. discriminate.
Qed.