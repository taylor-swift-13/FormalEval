Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Open Scope string_scope.

Inductive is_correctly_bracketed : string -> Prop :=
  | cb_nil    : is_correctly_bracketed ""
  | cb_nest   : forall l,
                  is_correctly_bracketed l ->
                  is_correctly_bracketed ("<" ++ l ++ ">")
  | cb_concat : forall l1 l2,
                  is_correctly_bracketed l1 ->
                  is_correctly_bracketed l2 ->
                  is_correctly_bracketed (l1 ++ l2).

Definition problem_56_pre (brackets : string) : Prop :=
    Forall (fun c => c = "<"%char \/ c = ">"%char) (list_ascii_of_string brackets).

Definition problem_56_spec (brackets : string) (b : bool) : Prop :=
  b = true <-> is_correctly_bracketed brackets.

Example problem_56_test_case_1 :
  problem_56_spec "><<><><><>>>><><" false.
Proof.
  unfold problem_56_spec.
  split.
  - intros H. discriminate H.
  - intros Hcb.
    assert (forall s, is_correctly_bracketed s -> s = "" \/ exists t, s = "<" ++ t) as Hstart.
    { intros s0 H0.
      induction H0 as [| l Hl | l1 l2 H1 IH1 H2 IH2].
      - left. reflexivity.
      - right. exists (l ++ ">"). simpl. reflexivity.
      - destruct IH1 as [Hz | [t Ht]].
        + rewrite Hz. simpl. apply IH2.
        + rewrite Ht. simpl. right. exists (t ++ l2). simpl. reflexivity.
    }
    specialize (Hstart _ Hcb).
    destruct Hstart as [Hz | [t Heq]].
    + discriminate Hz.
    + simpl in Heq. discriminate Heq.
Qed.