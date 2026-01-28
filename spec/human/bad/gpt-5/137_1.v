Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope R_scope.

Example problem_137_test_case_1 :
  problem_137_spec (VInt 1%Z) (VInt 2%Z) (Some (VInt 2%Z)).
Proof.
  unfold problem_137_spec.
  unfold compare_one_impl.
  simpl.
  assert (HltR : IZR 1%Z < IZR 2%Z) by (apply IZR_lt; lia).
  unfold Rlt_bool.
  destruct (Rlt_dec (IZR 1%Z) (IZR 2%Z)) as [Hlt|Hnlt].
  - reflexivity.
  - exfalso; apply Hnlt; exact HltR.
Qed.