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

Lemma is_ceil_2_1p38 : is_ceil 1.3807739357525621 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Lemma is_ceil_1_0p13 : is_ceil 0.13158576006729072 1%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Lemma is_ceil_1_0p9 : is_ceil 0.9 1%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Example test_problem_133 :
  problem_133_spec [1.3807739357525621%R; 0.13158576006729072%R; 0.9%R] 6%Z.
Proof.
  unfold problem_133_spec.
  exists [2%Z; 1%Z; 1%Z].
  split.
  - constructor.
    + apply is_ceil_2_1p38.
    + constructor.
      * apply is_ceil_1_0p13.
      * constructor.
        -- apply is_ceil_1_0p9.
        -- constructor.
  - simpl.
    reflexivity.
Qed.