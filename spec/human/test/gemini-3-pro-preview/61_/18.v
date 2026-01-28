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

Fixpoint bal (n : nat) (s : list ascii) : option nat :=
  match s with
  | [] => Some n
  | c :: s' =>
      if Ascii.eqb c "("%char then bal (S n) s'
      else if Ascii.eqb c ")"%char then
             match n with
             | 0 => None
             | S n' => bal n' s'
             end
           else None
  end.

Lemma bal_split : forall l1 l2 n,
  bal n (l1 ++ l2) = match bal n l1 with
                     | Some n' => bal n' l2
                     | None => None
                     end.
Proof.
  induction l1; simpl; intros.
  - reflexivity.
  - destruct (Ascii.eqb a "("%char).
    + apply IHl1.
    + destruct (Ascii.eqb a ")"%char).
      * destruct n; [reflexivity|apply IHl1].
      * reflexivity.
Qed.

Lemma is_correctly_bracketed_sound : forall l,
  is_correctly_bracketed l -> forall n, bal n l = Some n.
Proof.
  induction 1; intros.
  - simpl. reflexivity.
  - simpl. rewrite bal_split. rewrite IHis_correctly_bracketed.
    simpl. reflexivity.
  - rewrite bal_split. rewrite IHis_correctly_bracketed1. apply IHis_correctly_bracketed2.
Qed.

Example test_case_1 : problem_61_spec ["("%char; "("%char; ")"%char; ")"%char; ")"%char; "("%char; ")"%char] false.
Proof.
  unfold problem_61_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    apply is_correctly_bracketed_sound with (n:=0) in H.
    vm_compute in H.
    discriminate H.
Qed.