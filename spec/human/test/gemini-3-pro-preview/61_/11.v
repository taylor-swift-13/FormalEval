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

Fixpoint scan (s : list ascii) (n : nat) : option nat :=
  match s with
  | [] => Some n
  | c :: s' =>
    if (c =? "("%char)%char then scan s' (S n)
    else if (c =? ")"%char)%char then
      match n with
      | 0 => None
      | S n' => scan s' n'
      end
    else scan s' n
  end.

Lemma scan_app : forall l1 l2 n,
  scan (l1 ++ l2) n = match scan l1 n with Some n' => scan l2 n' | None => None end.
Proof.
  induction l1 as [|c l1 IH]; simpl; intros.
  - reflexivity.
  - destruct (c =? "("%char)%char.
    + apply IH.
    + destruct (c =? ")"%char)%char.
      * destruct n; simpl; [reflexivity|apply IH].
      * apply IH.
Qed.

Lemma is_correctly_bracketed_scan : forall l,
  is_correctly_bracketed l -> forall n, scan l n = Some n.
Proof.
  intros l H. induction H; intros.
  - simpl. reflexivity.
  - simpl. rewrite scan_app.
    rewrite IHis_correctly_bracketed.
    simpl. reflexivity.
  - rewrite scan_app. rewrite IHis_correctly_bracketed1. apply IHis_correctly_bracketed2.
Qed.

Example test_case_1 : problem_61_spec (list_ascii_of_string "()()(()())())(()") false.
Proof.
  unfold problem_61_spec.
  split.
  - intros H. discriminate.
  - intros H.
    apply is_correctly_bracketed_scan with (n:=0) in H.
    vm_compute in H.
    discriminate.
Qed.