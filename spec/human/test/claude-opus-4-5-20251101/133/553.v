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

Lemma is_ceil_IZR : forall z : Z, is_ceil (IZR z) z.
Proof.
  intro z.
  unfold is_ceil.
  split.
  - lra.
  - lra.
Qed.

Lemma is_ceil_neg_4_276 : is_ceil (-4.276480747131856) (-4%Z).
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_2 : is_ceil 3.2 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_2_509 : is_ceil (-2.5091429749847305) (-2%Z).
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_2_5 : is_ceil (-2.5) (-2%Z).
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_1_5 : is_ceil (-1.5) (-1%Z).
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

Lemma is_ceil_0_5 : is_ceil 0.5 1%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_2_5 : is_ceil 2.5 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_5 : is_ceil 3.5 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_4_5 : is_ceil 4.5 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [IZR (-5); -4.276480747131856; IZR (-4); 3.2; -2.5091429749847305; IZR (-3); -2.5; IZR (-2); -1.5; IZR (-1); -0.5; IZR 0; 0.5; IZR 2; 2.5; IZR 3; 3.5; IZR 4; 4.5; IZR 5; 3.5] 217%Z.
Proof.
  unfold problem_133_spec.
  exists [(-5)%Z; (-4)%Z; (-4)%Z; 4%Z; (-2)%Z; (-3)%Z; (-2)%Z; (-2)%Z; (-1)%Z; (-1)%Z; 0%Z; 0%Z; 1%Z; 2%Z; 3%Z; 3%Z; 4%Z; 4%Z; 5%Z; 5%Z; 4%Z].
  split.
  - constructor. apply is_ceil_IZR.
    constructor. apply is_ceil_neg_4_276.
    constructor. apply is_ceil_IZR.
    constructor. apply is_ceil_3_2.
    constructor. apply is_ceil_neg_2_509.
    constructor. apply is_ceil_IZR.
    constructor. apply is_ceil_neg_2_5.
    constructor. apply is_ceil_IZR.
    constructor. apply is_ceil_neg_1_5.
    constructor. apply is_ceil_IZR.
    constructor. apply is_ceil_neg_0_5.
    constructor. apply is_ceil_IZR.
    constructor. apply is_ceil_0_5.
    constructor. apply is_ceil_IZR.
    constructor. apply is_ceil_2_5.
    constructor. apply is_ceil_IZR.
    constructor. apply is_ceil_3_5.
    constructor. apply is_ceil_IZR.
    constructor. apply is_ceil_4_5.
    constructor. apply is_ceil_IZR.
    constructor. apply is_ceil_3_5.
    constructor.
  - simpl.
    reflexivity.
Qed.