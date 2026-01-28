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

Definition problem_134_spec (s : string) (b : bool) : Prop :=
  b = true <-> ends_with_single_letter_pred s.

Example test_apple_false : ~ (ends_with_single_letter_pred "apple").
Proof.
  unfold ends_with_single_letter_pred.
  intro H.
  destruct H as [pre [c [H1 [H2 H3]]]].
  unfold list_ascii_of_string in H1.
  simpl in H1.
  destruct pre.
  - inversion H1.
  - inversion H1.
    destruct H3 as [H3 | H3].
    + discriminate.
    + destruct H3 as [pre' H3].
      inversion H3.
Qed.

Example test_apple_spec : problem_134_spec "apple" false.
Proof.
  unfold problem_134_spec.
  split.
  - intro H. inversion H.
  - intro H. exfalso. apply test_apple_false. exact H.
Qed.