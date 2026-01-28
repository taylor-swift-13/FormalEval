Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition problem_127_pre (i1 i2 : Z * Z) : Prop :=
  let '(s1,e1) := i1 in
  let '(s2,e2) := i2 in s1 <= e1 /\ s2 <= e2.

Definition problem_127_spec (i1 i2 : Z * Z) (output : string) : Prop :=
  let (s1, e1) := i1 in
  let (s2, e2) := i2 in
  let s_inter := Z.max s1 s2 in
  let e_inter := Z.min e1 e2 in
  if Z.leb s_inter e_inter then
    let len_nat := Z.to_nat (e_inter - s_inter) in
    (prime (Z.of_nat len_nat) /\ output = "YES") \/
    (~prime (Z.of_nat len_nat) /\ output = "NO")
  else
    output = "NO".

Example test_intersection_12_12_and_12_12 : problem_127_spec (12, 12) (12, 12) "NO".
Proof.
  unfold problem_127_spec.
  simpl.
  right.
  split.
  - intro H.
    inversion H.
    lia.
  - reflexivity.
Qed.