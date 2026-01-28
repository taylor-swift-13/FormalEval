Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

(* Inductive definition of correctly bracketed strings *)
Inductive is_correctly_bracketed : string -> Prop :=
  | cb_nil    : is_correctly_bracketed ""
  | cb_nest   : forall l,
                  is_correctly_bracketed l ->
                  is_correctly_bracketed ("<" ++ l ++ ">")
  | cb_concat : forall l1 l2,
                  is_correctly_bracketed l1 ->
                  is_correctly_bracketed l2 ->
                  is_correctly_bracketed (l1 ++ l2).

(* Precondition definition *)
Definition problem_56_pre (brackets : string) : Prop :=
    Forall (fun c => c = "<"%char \/ c = ">"%char) (list_ascii_of_string brackets).

(* Specification definition *)
Definition problem_56_spec (brackets : string) (b : bool) : Prop :=
  b = true <-> is_correctly_bracketed brackets.

Fixpoint check_balance (s : string) (n : nat) : option nat :=
  match s with
  | EmptyString => Some n
  | String c s' =>
      if (ascii_dec c "<") then check_balance s' (S n)
      else if (ascii_dec c ">") then
        match n with
        | 0 => None
        | S n' => check_balance s' n'
        end
      else check_balance s' n
  end.

Lemma check_balance_append : forall s1 s2 n,
  check_balance (s1 ++ s2) n = 
    match check_balance s1 n with
    | Some n' => check_balance s2 n'
    | None => None
    end.
Proof.
  induction s1 as [|c s1 IH]; intros s2 n.
  - simpl. reflexivity.
  - simpl. destruct (ascii_dec c "<").
    + apply IH.
    + destruct (ascii_dec c ">").
      * destruct n.
        -- reflexivity.
        -- apply IH.
      * apply IH.
Qed.

Lemma is_correctly_bracketed_sound : forall s,
  is_correctly_bracketed s -> forall n, check_balance s n = Some n.
Proof.
  intros s H. induction H; intros n.
  - simpl. reflexivity.
  - simpl. rewrite check_balance_append. rewrite IHis_correctly_bracketed.
    simpl. reflexivity.
  - rewrite check_balance_append. rewrite IHis_correctly_bracketed1.
    apply IHis_correctly_bracketed2.
Qed.

Example test_correct_bracketing_neg : problem_56_spec "<<<>>>><<><><><>>>>><><" false.
Proof.
  unfold problem_56_spec.
  split.
  - intros H. discriminate.
  - intros H.
    apply is_correctly_bracketed_sound with (n:=0) in H.
    vm_compute in H.
    discriminate.
Qed.