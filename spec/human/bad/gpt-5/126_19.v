Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Sorting.Sorted.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_126_pre (l : list nat) : Prop := True.

Definition problem_126_spec (l : list nat) (b : bool) : Prop :=
  Sorted Nat.lt l <-> b = true.

Example problem_126_test_case_1 :
  problem_126_spec
    [Z.to_nat 3%Z; Z.to_nat 3%Z; Z.to_nat 3%Z; Z.to_nat 3%Z;
     Z.to_nat 2%Z; Z.to_nat 2%Z; Z.to_nat 2%Z; Z.to_nat 2%Z;
     Z.to_nat 1%Z; Z.to_nat 1%Z]
    false.
Proof.
  unfold problem_126_spec.
  split.
  - intros Hs.
    exfalso.
    inversion Hs as [|x l Hsorted Hhd]; subst.
    inversion Hhd as [|y l' Hy Hd']; subst.
    apply (Nat.lt_irrefl (Z.to_nat 3%Z)).
    exact Hy.
  - intros H.
    elimtype False. discriminate H.
Qed.