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

Lemma is_ceil_3_14_4 : is_ceil 3.14 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_8_09_neg_8 : is_ceil (-8.09) (-8)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_0_84_1 : is_ceil 0.8407610504622577 1%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_1_52_2 : is_ceil 1.5224939717635053 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_9_99_neg_9 : is_ceil (-9.99) (-9)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_6_28_7 : is_ceil 6.28 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_1_62_2 : is_ceil 1.62 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [3.14; -8.09; 0.8407610504622577; 1.5224939717635053; -9.99; 6.28; 1.62; -8.09] 283%Z.
Proof.
  unfold problem_133_spec.
  exists [4%Z; (-8)%Z; 1%Z; 2%Z; (-9)%Z; 7%Z; 2%Z; (-8)%Z].
  split.
  - constructor.
    + apply is_ceil_3_14_4.
    + constructor.
      * apply is_ceil_neg_8_09_neg_8.
      * constructor.
        -- apply is_ceil_0_84_1.
        -- constructor.
           ++ apply is_ceil_1_52_2.
           ++ constructor.
              ** apply is_ceil_neg_9_99_neg_9.
              ** constructor.
                 --- apply is_ceil_6_28_7.
                 --- constructor.
                     +++ apply is_ceil_1_62_2.
                     +++ constructor.
                         *** apply is_ceil_neg_8_09_neg_8.
                         *** constructor.
  - simpl.
    reflexivity.
Qed.