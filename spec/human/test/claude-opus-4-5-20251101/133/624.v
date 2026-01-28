Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition is_ceil (x : R) (z : Z) : Prop :=
  (IZR z - 1 < x) /\ (x <= IZR z).

Definition problem_133_pre (lst : list R) : Prop := True.

Definition problem_133_spec (lst : list R) (s : Z) : Prop :=
  exists zs : list Z,
    Forall2 is_ceil lst zs /\
    s = fold_right Z.add 0%Z (map (fun z => Z.mul z z) zs).

Lemma is_ceil_neg_0_1 : is_ceil (-0.1) 0%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_0_5 : is_ceil (-0.5) 0%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_0_9 : is_ceil (-0.9) 0%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [-0.1; -0.5; -0.9] 0%Z.
Proof.
  unfold problem_133_spec.
  exists [0%Z; 0%Z; 0%Z].
  split.
  - constructor.
    + apply is_ceil_neg_0_1.
    + constructor.
      * apply is_ceil_neg_0_5.
      * constructor.
        -- apply is_ceil_neg_0_9.
        -- constructor.
  - simpl.
    reflexivity.
Qed.