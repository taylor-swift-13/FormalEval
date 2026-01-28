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

Lemma is_ceil_neg1_1 : is_ceil (-1.1) (-1)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_2_832781453766651 : is_ceil 2.832781453766651 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg2_9445611166646914 : is_ceil (-2.9445611166646914) (-2)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_4_6 : is_ceil 4.6 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_5_1 : is_ceil 5.1 6%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_2_964251544523867 : is_ceil 2.964251544523867 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [(-1.1); 2.832781453766651; (-2.9445611166646914); 4.6; 5.1; 2.964251544523867; IZR 6; (-1.1)] 121%Z.
Proof.
  unfold problem_133_spec.
  exists [(-1)%Z; 3%Z; (-2)%Z; 5%Z; 6%Z; 3%Z; 6%Z; (-1)%Z].
  split.
  - constructor.
    + apply is_ceil_neg1_1.
    + constructor.
      * apply is_ceil_2_832781453766651.
      * constructor.
        -- apply is_ceil_neg2_9445611166646914.
        -- constructor.
           ++ apply is_ceil_4_6.
           ++ constructor.
              ** apply is_ceil_5_1.
              ** constructor.
                 --- apply is_ceil_2_964251544523867.
                 --- constructor.
                     +++ apply is_ceil_IZR.
                     +++ constructor.
                         *** apply is_ceil_neg1_1.
                         *** constructor.
  - simpl.
    reflexivity.
Qed.