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

Lemma is_ceil_0_1_1 : is_ceil (1/10) 1%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_6_851_7 : is_ceil (6851261387881998 / 1000000000000000) 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_2_4 : is_ceil (16/5) 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_699_4 : is_ceil (3699349421992388 / 1000000000000000) 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_287_4 : is_ceil (3287852215132159 / 1000000000000000) 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_6_7_7 : is_ceil (67/10) 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [1/10; 6851261387881998 / 1000000000000000; 16/5; 3699349421992388 / 1000000000000000; 3287852215132159 / 1000000000000000; 67/10; 67/10] 196%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; 7%Z; 4%Z; 4%Z; 4%Z; 7%Z; 7%Z].
  split.
  - constructor.
    + apply is_ceil_0_1_1.
    + constructor.
      * apply is_ceil_6_851_7.
      * constructor.
        -- apply is_ceil_3_2_4.
        -- constructor.
           ++ apply is_ceil_3_699_4.
           ++ constructor.
              ** apply is_ceil_3_287_4.
              ** constructor.
                 --- apply is_ceil_6_7_7.
                 --- constructor.
                     +++ apply is_ceil_6_7_7.
                     +++ constructor.
  - simpl.
    reflexivity.
Qed.