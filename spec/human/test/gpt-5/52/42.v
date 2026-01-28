Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list R) : Prop := True.

Definition problem_52_spec (l : list R) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < IZR t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [3.5%R; 2.6445924145352944%R; 2.2%R; 1.1%R] 3%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros HAll. exfalso.
    specialize (HAll 3.5%R).
    assert (Hin : In 3.5%R [3.5%R; 2.6445924145352944%R; 2.2%R; 1.1%R]) by (simpl; left; reflexivity).
    specialize (HAll Hin).
    lra.
  - intros Hfalse.
    exfalso. discriminate Hfalse.
Qed.