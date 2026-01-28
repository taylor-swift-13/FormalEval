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

Fixpoint verify (s : string) (n : nat) : option nat :=
  match s with
  | EmptyString => Some n
  | String c s' => 
      if Ascii.eqb c "<" then verify s' (S n)
      else if Ascii.eqb c ">" then
        match n with
        | 0 => None
        | S k => verify s' k
        end
      else verify s' n
  end.

Lemma verify_app : forall s1 s2 n,
  verify (s1 ++ s2) n = match verify s1 n with
                        | Some n' => verify s2 n'
                        | None => None
                        end.
Proof.
  induction s1; intros; simpl.
  - reflexivity.
  - destruct (Ascii.eqb a "<").
    + apply IHs1.
    + destruct (Ascii.eqb a ">").
      * destruct n; simpl.
        -- reflexivity.
        -- apply IHs1.
      * apply IHs1.
Qed.

Lemma verify_cb : forall s, is_correctly_bracketed s -> forall n, verify s n = Some n.
Proof.
  intros s H. induction H; intros.
  - simpl. reflexivity.
  - simpl. rewrite verify_app. simpl. rewrite IHis_correctly_bracketed.
    simpl. destruct n; reflexivity.
  - rewrite verify_app. rewrite IHis_correctly_bracketed1. apply IHis_correctly_bracketed2.
Qed.

Example test_correct_bracketing_false : 
  problem_56_spec "<><>>>><<<<><>>><<>><>>>><<<<><<<<<<<<>>><><><>>>>><<>>>><<<<><>>>><<<<><>>>><" false.
Proof.
  unfold problem_56_spec.
  split.
  - intros H. discriminate.
  - intros H.
    apply verify_cb with (n:=0) in H.
    vm_compute in H.
    discriminate.
Qed.