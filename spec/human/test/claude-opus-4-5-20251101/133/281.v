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

Lemma is_ceil_0_1 : is_ceil 0.1 1%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_1_5_2 : is_ceil 1.5 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_2_8396588982482287 : is_ceil (-2.8396588982482287) (-2)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_2_4936669865395658 : is_ceil 2.4936669865395658 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_4_234081562814888 : is_ceil 4.234081562814888 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_6_851261387881998 : is_ceil 6.851261387881998 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_0_7284547363306774 : is_ceil 0.7284547363306774 1%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_6_7 : is_ceil 6.7 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [0.1; 1.5; -2.8396588982482287; 2.4936669865395658; 4.234081562814888; 6.851261387881998; 0.7284547363306774; 6.7] 142%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; 2%Z; (-2)%Z; 3%Z; 5%Z; 7%Z; 1%Z; 7%Z].
  split.
  - constructor.
    + apply is_ceil_0_1.
    + constructor.
      * apply is_ceil_1_5_2.
      * constructor.
        -- apply is_ceil_neg_2_8396588982482287.
        -- constructor.
           ++ apply is_ceil_2_4936669865395658.
           ++ constructor.
              ** apply is_ceil_4_234081562814888.
              ** constructor.
                 --- apply is_ceil_6_851261387881998.
                 --- constructor.
                     +++ apply is_ceil_0_7284547363306774.
                     +++ constructor.
                         *** apply is_ceil_6_7.
                         *** constructor.
  - simpl.
    reflexivity.
Qed.