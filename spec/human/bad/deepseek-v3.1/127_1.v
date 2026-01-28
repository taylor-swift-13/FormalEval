Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Arith.PeanoNat.

Open Scope Z_scope.
Open Scope string_scope.

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

Example test_case_1 : problem_127_spec (1, 2) (2, 3) "NO".
Proof.
  unfold problem_127_spec.
  simpl.
  right.
  split.
  - intro H.
    assert (H0 : Z.of_nat 0 > 1 \/ (exists x, Z.divide x (Z.of_nat 0) /\ prime x)).
    { left. compute. discriminate. }
    apply Znumtheory.prime_divisors in H.
    destruct H as [H H1].
    apply H1 in H0.
    destruct H0 as [x [H2 H3]].
    compute in H2.
    contradiction.
  - reflexivity.
Qed.