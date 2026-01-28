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

Lemma is_ceil_1_1_2 : is_ceil (11/10) 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_2_5_3 : is_ceil (5/2) 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_3_7_neg_3 : is_ceil (-37/10) (-3)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_4_6_neg_4 : is_ceil (-46/10) (-4)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_special_neg_2 : is_ceil (-28396588982482287/10000000000000000) (-2)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_5_2_6 : is_ceil (52/10) 6%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [11/10; 5/2; -37/10; -46/10; -28396588982482287/10000000000000000; 52/10; IZR 6] 114%Z.
Proof.
  unfold problem_133_spec.
  exists [2%Z; 3%Z; (-3)%Z; (-4)%Z; (-2)%Z; 6%Z; 6%Z].
  split.
  - constructor.
    + apply is_ceil_1_1_2.
    + constructor.
      * apply is_ceil_2_5_3.
      * constructor.
        -- apply is_ceil_neg_3_7_neg_3.
        -- constructor.
           ++ apply is_ceil_neg_4_6_neg_4.
           ++ constructor.
              ** apply is_ceil_special_neg_2.
              ** constructor.
                 --- apply is_ceil_5_2_6.
                 --- constructor.
                     +++ apply is_ceil_IZR.
                     +++ constructor.
  - simpl.
    reflexivity.
Qed.