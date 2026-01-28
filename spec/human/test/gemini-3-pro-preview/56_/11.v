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

(* Helper function to verify nesting balance *)
Fixpoint balance (s : string) (n : nat) : option nat :=
  match s with
  | EmptyString => Some n
  | String c s' =>
      if Ascii.eqb c "<"%char then balance s' (S n)
      else if Ascii.eqb c ">"%char then
        match n with
        | 0 => None
        | S n' => balance s' n'
        end
      else balance s' n
  end.

(* Lemma: appending strings composes balance effects *)
Lemma balance_append : forall s1 s2 n,
  balance (s1 ++ s2) n = match balance s1 n with
                         | Some n' => balance s2 n'
                         | None => None
                         end.
Proof.
  induction s1 as [|c s1 IH]; intros s2 n.
  - simpl. reflexivity.
  - simpl.
    destruct (Ascii.eqb c "<"%char).
    + apply IH.
    + destruct (Ascii.eqb c ">"%char).
      * destruct n.
        -- reflexivity.
        -- apply IH.
      * apply IH.
Qed.

(* Lemma: correctly bracketed strings preserve balance and end at starting depth *)
Lemma correct_balance_valid : forall s,
  is_correctly_bracketed s -> forall n, balance s n = Some n.
Proof.
  intros s H. induction H; intros n.
  - simpl. reflexivity.
  - simpl. 
    rewrite balance_append.
    rewrite IHis_correctly_bracketed.
    simpl.
    replace (Ascii.eqb ">"%char "<"%char) with false by reflexivity.
    replace (Ascii.eqb ">"%char ">"%char) with true by reflexivity.
    reflexivity.
  - rewrite balance_append.
    rewrite IHis_correctly_bracketed1.
    apply IHis_correctly_bracketed2.
Qed.

(* Example Proof for Test Case: input = "<><><<><>><>><<>", output = false *)
Example test_correct_bracketing_basic : problem_56_spec "<><><<><>><>><<>" false.
Proof.
  unfold problem_56_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    apply correct_balance_valid with (n:=0) in H.
    vm_compute in H.
    discriminate H.
Qed.