Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

Inductive check_parens_inner_rel : list ascii -> nat -> bool -> Prop :=
  | cpir_nil_zero : check_parens_inner_rel [] 0 true
  | cpir_nil_nonzero : forall n, n <> 0 -> check_parens_inner_rel [] n false
  | cpir_lparen : forall t counter result,
      check_parens_inner_rel t (S counter) result ->
      check_parens_inner_rel ("("%char :: t) counter result
  | cpir_rparen_zero : forall t counter,
      counter = 0 ->
      check_parens_inner_rel (")"%char :: t) counter false
  | cpir_rparen : forall t counter n' result,
      counter = S n' ->
      check_parens_inner_rel t n' result ->
      check_parens_inner_rel (")"%char :: t) counter result
  | cpir_other : forall c t counter result,
      c <> "("%char -> c <> ")"%char ->
      check_parens_inner_rel t counter result ->
      check_parens_inner_rel (c :: t) counter result.

Inductive is_balanced_rel : list ascii -> bool -> Prop :=
  | ibr_base : forall l result, check_parens_inner_rel l 0 result -> is_balanced_rel l result.

Inductive concat_rel : list ascii -> list ascii -> list ascii -> Prop :=
  | concr_base : forall l1 l2, concat_rel l1 l2 (l1 ++ l2).

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

Definition problem_119_pre (inputs : list string) : Prop :=
  length inputs = 2 /\ Forall (fun s =>
    let l := list_ascii_of_string s in
    Forall (fun c => c = "("%char \/ c = ")"%char) l) inputs.

Definition problem_119_spec (inputs : list string) (output : string) : Prop :=
  (exists s1 s2 s12,
     map list_ascii_of_string inputs = [s1; s2] /\
     concat_rel s1 s2 s12 /\
     is_balanced_rel s12 true /\
     output = "Yes") \/
  (exists s1 s2 s21,
     map list_ascii_of_string inputs = [s1; s2] /\
     concat_rel s2 s1 s21 /\
     is_balanced_rel s21 true /\
     output = "Yes") \/
  ((forall s1 s2, map list_ascii_of_string inputs <> [s1; s2] \/
    (forall s12, concat_rel s1 s2 s12 -> is_balanced_rel s12 false) /\
    (forall s21, concat_rel s2 s1 s21 -> is_balanced_rel s21 false)) /\
   output = "No").

(* 定义一个函数形式判定辅助 *)
Fixpoint check_parens_inner_bool (l : list ascii) (counter : nat) : bool :=
  match l with
  | [] => Nat.eqb counter 0
  | c :: t =>
    if ascii_dec c "(" then
      check_parens_inner_bool t (S counter)
    else if ascii_dec c ")" then
      match counter with
      | 0 => false
      | S n' => check_parens_inner_bool t n'
      end
    else
      check_parens_inner_bool t counter
  end.

Lemma check_parens_inner_bool_rel : forall l n b,
  check_parens_inner_bool l n = b -> check_parens_inner_rel l n b.
Proof.
  induction l as [|c t IH]; intros n b H.
  - simpl in H. destruct (Nat.eqb n 0) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor.
    + apply Nat.eqb_neq in E. constructor. assumption.
  - simpl in H.
    destruct (ascii_dec c "(") as [Heq | Hneq].
    + eapply cpir_lparen. apply IH. assumption.
    + destruct (ascii_dec c ")") as [Heq'|Hneq'].
      * destruct n as [| n'].
        { simpl in H. discriminate. }
        eapply cpir_rparen; [reflexivity|].
        eapply IH. assumption.
      * eapply cpir_other; try assumption.
        eapply IH. assumption.
Qed.

Lemma is_balanced_rel_equiv : forall l b,
  is_balanced_rel l b <-> check_parens_inner_bool l 0 = b.
Proof.
  split.
  - intros [H]. inversion H. subst. clear H.
    induction l as [|a t IH]; simpl.
    + destruct b; constructor.
      * apply cpir_nil_zero.
      * apply cpir_nil_nonzero. congruence.
    + destruct (ascii_dec a "(").
      * constructor. apply IH.
      * destruct (ascii_dec a ")").
        -- destruct b.
           ++ simpl in H0; inversion H0; subst.
              destruct n; try discriminate.
              apply IH.
           ++ constructor.
              inversion H0; subst.
              destruct n; try discriminate.
              apply IH.
        -- constructor.
           inversion H0; subst.
           apply IH.
  - intros Hbool. apply ibr_base. eapply check_parens_inner_bool_rel. apply Hbool.
Qed.

Example test_case_119 :
  problem_119_spec ["()("; ")"] "Yes".
Proof.
  unfold problem_119_spec.
  left.
  exists (list_ascii_of_string "()(").
  exists (list_ascii_of_string ")").
  exists ((list_ascii_of_string "()(") ++ (list_ascii_of_string ")")).
  split.
  - simpl. reflexivity.
  - split.
    + constructor. reflexivity.
    + split.
      * apply ibr_base.
        eapply check_parens_inner_bool_rel.
        simpl.
        (* 逐步计算： '(' => counter=1; ')' => counter=0; '(' => counter=1; ')' => counter=0 *)
        (* 最终返回 true *)
        reflexivity.
      * reflexivity.
Qed.