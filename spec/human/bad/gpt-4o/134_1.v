Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.
Import ListNotations.

Definition space : ascii := Ascii.ascii_of_nat 32.

Definition is_alpha (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122).

Definition ends_with_single_letter_pred (s : string) : Prop :=
  let l := list_ascii_of_string s in
  exists pre c,
    l = pre ++ [c] /\
    is_alpha c /\
    (pre = [] \/ exists pre', pre = pre' ++ [space]).

Definition problem_134_pre (s : string) : Prop := True.

Definition problem_134_spec (s : string) (b : bool) : Prop :=
  b = true <-> ends_with_single_letter_pred s.

Example test_case_1 : problem_134_spec "apple" false.
Proof.
  unfold problem_134_spec.
  split.
  - intros H. inversion H.
  - intros [pre [c [H1 [H2 H3]]]].
    unfold list_ascii_of_string in H1.
    simpl in H1.
    destruct pre.
    + simpl in H1. inversion H1.
      subst. unfold is_alpha in H2. simpl in H2.
      destruct H2 as [[H2a H2b] | [H2a H2b]]; lia.
    + destruct pre.
      * simpl in H1. inversion H1. subst.
        unfold is_alpha in H2. simpl in H2.
        destruct H2 as [[H2a H2b] | [H2a H2b]]; lia.
      * simpl in H1. inversion H1.
Qed.