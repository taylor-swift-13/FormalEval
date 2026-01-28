(* 引入Coq标准库，用于列表（List）和ASCII字符（Ascii）的定义 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Import ListNotations.

Open Scope string_scope.

(* Definition of what it means for a string to be correctly bracketed *)
Inductive is_correctly_bracketed : string -> Prop :=
  | cb_nil    : is_correctly_bracketed ""
  | cb_nest   : forall l,
                  is_correctly_bracketed l ->
                  is_correctly_bracketed ("<" ++ l ++ ">")
  | cb_concat : forall l1 l2,
                  is_correctly_bracketed l1 ->
                  is_correctly_bracketed l2 ->
                  is_correctly_bracketed (l1 ++ l2).

(* Precondition: the string consists of only < and > characters *)
Definition problem_56_pre (brackets : string) : Prop :=
    Forall (fun c => c = "<"%char \/ c = ">"%char) (list_ascii_of_string brackets).

(* Specification: the boolean result indicates correct bracketing *)
Definition problem_56_spec (brackets : string) (b : bool) : Prop :=
  b = true <-> is_correctly_bracketed brackets.

(* Helper function to count the balance of brackets *)
Fixpoint bracket_balance (s : string) (balance : nat) : option nat :=
  match s with
  | "" => Some balance
  | String "<" s' => bracket_balance s' (balance + 1)
  | String ">" s' =>
      match balance with
      | 0 => None
      | S n => bracket_balance s' n
      end
  | String _ s' => bracket_balance s' balance
  end.

(* Correct bracketing function *)
Definition correct_bracketing (s : string) : bool :=
  match bracket_balance s 0 with
  | Some 0 => true
  | _ => false
  end.

(* Prove that correct_bracketing satisfies the specification for given test case *)
Example correct_bracketing_test : problem_56_spec "<>" true.
Proof.
  unfold problem_56_spec.
  split.
  - intros H. apply cb_nest. apply cb_nil.
  - intros H. unfold correct_bracketing. simpl.
    (* Evaluate bracket_balance for "<>" *)
    unfold bracket_balance. simpl.
    (* Show that it evaluates to Some 0 *)
    reflexivity.
Qed.