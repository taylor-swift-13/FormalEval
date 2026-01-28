Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

(* 子列表定义 *)
Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, is_subsequence [] l
  | sub_cons_match : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_skip : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

Definition problem_29_pre (input : list string) : Prop := True.

Definition problem_29_spec (input : list string) (substring : string) (output : list string) : Prop :=
  is_subsequence output input /\
  (forall s, In s output <-> (In s input /\ String.prefix substring s = true)).

Example test_case_empty_output :
  let input := [""; "john"] in
  let output := [] in
  problem_29_spec input "a" output.
Proof.
  cbn.
  split.
  - (* is_subsequence [] input *)
    constructor.
  - (* forall s, In s output <-> (In s input /\ prefix "a" s = true) *)
    intros s.
    split; intros H.
    + inversion H.
    + destruct H as [_prefix].
      simpl in H.
      inversion H.
Qed.