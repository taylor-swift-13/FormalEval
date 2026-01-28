Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope string_scope.

(* Recursively check if the first string is a prefix of the second *)
Fixpoint is_prefix (p s: string) : bool :=
  match p, s with
  | EmptyString, _ => true
  | String a p', String b s' => if Ascii.eqb a b then is_prefix p' s' else false
  | _, _ => false
  end.

(* Filter the list of strings by the given prefix *)
Fixpoint filter_by_prefix (lst: list string) (prefix: string) : list string :=
  match lst with
  | [] => []
  | s :: rest => if is_prefix prefix s
                then s :: filter_by_prefix rest prefix
                else filter_by_prefix rest prefix
  end.

Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, is_subsequence [] l
  | sub_cons_match : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_skip : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

Definition problem_29_spec (input : list string) (substring : string) (output : list string) : Prop :=
  is_subsequence output input /\
  (forall s, In s output <-> (In s input /\ is_prefix substring s = true)).

Example filter_by_prefix_test:
  let input := [""; "john"] in
  let output := filter_by_prefix input "a" in
  problem_29_spec input "a" output.
Proof.
  unfold problem_29_spec.
  split.
  - unfold filter_by_prefix. apply sub_nil.
  - intros s. split.
    + intros H. exfalso. destruct H.
    + intros [H _]. exfalso. destruct H.
Qed.