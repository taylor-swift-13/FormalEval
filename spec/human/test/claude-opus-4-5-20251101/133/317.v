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

Lemma is_ceil_1_1 : is_ceil (1 + /10) 2.
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_2_5 : is_ceil (2 + /2) 3.
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_neg_4_7 : is_ceil (-4716809497407311 / 1000000000000000) (-4).
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_4_2 : is_ceil (4234081562814888 / 1000000000000000) 5.
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_neg_6_5 : is_ceil (-(6 + /2)) (-6).
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Example test_problem_133 :
  problem_133_spec [1 + /10; 2 + /2; -4716809497407311 / 1000000000000000; IZR 5; 4234081562814888 / 1000000000000000; -(6 + /2); IZR 6; 1 + /10] 155%Z.
Proof.
  unfold problem_133_spec.
  exists [2%Z; 3%Z; (-4)%Z; 5%Z; 5%Z; (-6)%Z; 6%Z; 2%Z].
  split.
  - constructor.
    + apply is_ceil_1_1.
    + constructor.
      * apply is_ceil_2_5.
      * constructor.
        -- apply is_ceil_neg_4_7.
        -- constructor.
           ++ apply is_ceil_IZR.
           ++ constructor.
              ** apply is_ceil_4_2.
              ** constructor.
                 --- apply is_ceil_neg_6_5.
                 --- constructor.
                     +++ apply is_ceil_IZR.
                     +++ constructor.
                         *** apply is_ceil_1_1.
                         *** constructor.
  - simpl.
    reflexivity.
Qed.