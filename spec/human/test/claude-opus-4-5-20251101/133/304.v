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

Lemma is_ceil_1_1_2 : is_ceil (1 + 1/10) 2.
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_neg_3_7_neg_3 : is_ceil (-(3 + 7/10)) (-3).
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_neg_4_6_neg_4 : is_ceil (-(4 + 6/10)) (-4).
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_neg_4_276874536373084_neg_4 : is_ceil (-(4 + 276874536373084/1000000000000000)) (-4).
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_neg_5_2_neg_5 : is_ceil (-(5 + 2/10)) (-5).
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_neg_9_99_neg_9 : is_ceil (-(9 + 99/100)) (-9).
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Example test_problem_133 :
  problem_133_spec [1 + 1/10; -(3 + 7/10); -(4 + 6/10); -(4 + 276874536373084/1000000000000000); -(5 + 2/10); -(9 + 99/100); IZR (-6)] 187%Z.
Proof.
  unfold problem_133_spec.
  exists [2%Z; (-3)%Z; (-4)%Z; (-4)%Z; (-5)%Z; (-9)%Z; (-6)%Z].
  split.
  - constructor.
    + apply is_ceil_1_1_2.
    + constructor.
      * apply is_ceil_neg_3_7_neg_3.
      * constructor.
        -- apply is_ceil_neg_4_6_neg_4.
        -- constructor.
           ++ apply is_ceil_neg_4_276874536373084_neg_4.
           ++ constructor.
              ** apply is_ceil_neg_5_2_neg_5.
              ** constructor.
                 --- apply is_ceil_neg_9_99_neg_9.
                 --- constructor.
                     +++ apply is_ceil_IZR.
                     +++ constructor.
  - simpl.
    reflexivity.
Qed.