Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_never_odd_or_even :
  problem_48_spec "never odd or even" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H i Hi.
    exfalso.
    discriminate H.
  - intros Hpal.
    set (i := 4%nat).
    assert (Hi: (i < String.length "never odd or even" / 2)%nat).
    { subst i. vm_compute. lia. }
    specialize (Hpal i Hi).
    assert (Hneq: String.get i "never odd or even" <> String.get (String.length "never odd or even" - 1 - i) "never odd or even").
    { subst i. intro Heq. vm_compute in Heq. discriminate Heq. }
    exfalso.
    apply Hneq.
    exact Hpal.
Qed.