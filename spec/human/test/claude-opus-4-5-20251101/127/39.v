Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Import ListNotations.
Open Scope Z_scope.

Definition problem_127_pre (i1 i2 : Z * Z) : Prop :=
  let '(s1,e1) := i1 in
  let '(s2,e2) := i2 in (s1 <= e1)%Z /\ (s2 <= e2)%Z.

Definition problem_127_spec (i1 i2 : Z * Z) (output : string) : Prop :=
  let (s1, e1) := i1 in
  let (s2, e2) := i2 in
  let s_inter := Z.max s1 s2 in
  let e_inter := Z.min e1 e2 in
  if Z.leb s_inter e_inter then
    let len_nat := Z.to_nat (e_inter - s_inter) in
    (prime (Z.of_nat len_nat) /\ output = "YES"%string) \/
    (~prime (Z.of_nat len_nat) /\ output = "NO"%string)
  else
    output = "NO"%string.

Lemma not_prime_0 : ~prime 0.
Proof.
  intro H.
  destruct H as [H1 H2].
  lia.
Qed.

Example test_intersection_1 : problem_127_spec (0%Z, 3%Z) (0%Z, 0%Z) "NO"%string.
Proof.
  unfold problem_127_spec.
  simpl.
  right.
  split.
  - apply not_prime_0.
  - reflexivity.
Qed.