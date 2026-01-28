Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Sorting.Sorted.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_126_pre (l : list nat) : Prop := True.

Definition problem_126_spec (l : list nat) (b : bool) : Prop :=
  Sorted Nat.lt l <-> b = true.

Example problem_126_test_case_1 :
  problem_126_spec [Z.to_nat 1%Z; Z.to_nat 3%Z; Z.to_nat 2%Z; Z.to_nat 4%Z; Z.to_nat 5%Z; Z.to_nat 6%Z; Z.to_nat 7%Z] false.
Proof.
  unfold problem_126_spec.
  split.
  - intros H.
    exfalso.
    inversion H as [| ? ? Hsorted Hhd]; subst.
    inversion Hsorted as [| ? ? Hsorted2 Hhd2]; subst.
    inversion Hhd2 as [| ? ? ? Hlt]; subst.
    lia.
  - intros H.
    exfalso.
    discriminate H.
Qed.