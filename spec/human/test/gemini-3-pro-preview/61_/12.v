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

Fixpoint bal (l : list ascii) (n : nat) : option nat :=
  match l with
  | [] => Some n
  | c :: s' =>
      if (Ascii.eqb c "("%char) then bal s' (S n)
      else if (Ascii.eqb c ")"%char) then
        match n with
        | 0 => None
        | S n' => bal s' n'
        end
      else bal s' n
  end.

Lemma bal_app : forall l1 l2 n,
  bal (l1 ++ l2) n = match bal l1 n with Some n' => bal l2 n' | None => None end.
Proof.
  induction l1; intros; simpl.
  - reflexivity.
  - destruct (Ascii.eqb a "("%char).
    + apply IHl1.
    + destruct (Ascii.eqb a ")"%char).
      * destruct n.
        -- reflexivity.
        -- apply IHl1.
      * apply IHl1.
Qed.

Lemma correct_implies_bal : forall l,
  is_correctly_bracketed l -> forall n, bal l n = Some n.
Proof.
  intros l H. induction H; intros.
  - reflexivity.
  - simpl. replace (Ascii.eqb "("%char "("%char) with true by reflexivity.
    rewrite bal_app.
    rewrite IHis_correctly_bracketed.
    simpl. replace (Ascii.eqb ")"%char "("%char) with false by reflexivity.
    replace (Ascii.eqb ")"%char ")"%char) with true by reflexivity.
    reflexivity.
  - rewrite bal_app.
    rewrite IHis_correctly_bracketed1.
    rewrite IHis_correctly_bracketed2.
    reflexivity.
Qed.

Example test_case_1 : problem_61_spec (list_ascii_of_string "()()(()())()))()") false.
Proof.
  unfold problem_61_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    apply correct_implies_bal with (n:=0) in H.
    vm_compute in H.
    discriminate H.
Qed.