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

Lemma is_ceil_1_5 : is_ceil (3/2) 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_2_9 : is_ceil (29/10) 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_2_49 : forall x : R, 2 < x -> x <= 3 -> is_ceil x 3%Z.
Proof.
  intros x H1 H2.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_4_23 : forall x : R, 4 < x -> x <= 5 -> is_ceil x 5%Z.
Proof.
  intros x H1 H2.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_6_85 : forall x : R, 6 < x -> x <= 7 -> is_ceil x 7%Z.
Proof.
  intros x H1 H2.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_6_7 : is_ceil (67/10) 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_7_41 : forall x : R, 7 < x -> x <= 8 -> is_ceil x 8%Z.
Proof.
  intros x H1 H2.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [3/2; 29/10; 5/2; 43/10; 69/10; 67/10; 15/2; 67/10; 3/2] 262%Z.
Proof.
  unfold problem_133_spec.
  exists [2%Z; 3%Z; 3%Z; 5%Z; 7%Z; 7%Z; 8%Z; 7%Z; 2%Z].
  split.
  - constructor.
    + unfold is_ceil. simpl. lra.
    + constructor.
      * unfold is_ceil. simpl. lra.
      * constructor.
        -- unfold is_ceil. simpl. lra.
        -- constructor.
           ++ unfold is_ceil. simpl. lra.
           ++ constructor.
              ** unfold is_ceil. simpl. lra.
              ** constructor.
                 --- unfold is_ceil. simpl. lra.
                 --- constructor.
                     +++ unfold is_ceil. simpl. lra.
                     +++ constructor.
                         *** unfold is_ceil. simpl. lra.
                         *** constructor.
                             ---- unfold is_ceil. simpl. lra.
                             ---- constructor.
  - simpl.
    reflexivity.
Qed.