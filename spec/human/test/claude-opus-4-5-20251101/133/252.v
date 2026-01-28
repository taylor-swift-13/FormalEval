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

Lemma is_ceil_2_5 : is_ceil (5/2) 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_3_7 : is_ceil (-37/10) (-3)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_4_234 : forall x : R, (4 < x /\ x <= 5) -> is_ceil x 5%Z.
Proof.
  intros x [H1 H2].
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_4_716 : forall x : R, (-5 < x /\ x <= -4) -> is_ceil x (-4)%Z.
Proof.
  intros x [H1 H2].
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_6_5 : is_ceil (-13/2) (-6)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_1_1 : is_ceil (11/10) 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [5/2; -37/10; 5; -4; IZR 5; -13/2; 11/10; 5] 149%Z.
Proof.
  unfold problem_133_spec.
  exists [3%Z; (-3)%Z; 5%Z; (-4)%Z; 5%Z; (-6)%Z; 2%Z; 5%Z].
  split.
  - constructor.
    + apply is_ceil_2_5.
    + constructor.
      * apply is_ceil_neg_3_7.
      * constructor.
        -- unfold is_ceil. simpl. lra.
        -- constructor.
           ++ unfold is_ceil. simpl. lra.
           ++ constructor.
              ** apply is_ceil_IZR.
              ** constructor.
                 --- apply is_ceil_neg_6_5.
                 --- constructor.
                     +++ apply is_ceil_1_1.
                     +++ constructor.
                         *** unfold is_ceil. simpl. lra.
                         *** constructor.
  - simpl.
    reflexivity.
Qed.