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

Lemma is_ceil_4_234 : forall x : R, (4 < x) -> (x <= 5) -> is_ceil x 5%Z.
Proof.
  intros x H1 H2.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_4_716 : forall x : R, (-5 < x) -> (x <= -4) -> is_ceil x (-4)%Z.
Proof.
  intros x H1 H2.
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

Lemma is_ceil_neg_3_33 : forall x : R, (-4 < x) -> (x <= -3) -> is_ceil x (-3)%Z.
Proof.
  intros x H1 H2.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Definition val1 : R := 5/2.
Definition val2 : R := -37/10.
Definition val3 : R := 4234081562814888 / 1000000000000000.
Definition val4 : R := -4716809497407311 / 1000000000000000.
Definition val5 : R := IZR 5.
Definition val6 : R := -13/2.
Definition val7 : R := -333042479327025 / 100000000000000.
Definition val8 : R := -333042479327025 / 100000000000000.
Definition val9 : R := -13/2.

Example test_problem_133 :
  problem_133_spec [val1; val2; val3; val4; val5; val6; val7; val8; val9] 174%Z.
Proof.
  unfold problem_133_spec.
  exists [3%Z; (-3)%Z; 5%Z; (-4)%Z; 5%Z; (-6)%Z; (-3)%Z; (-3)%Z; (-6)%Z].
  split.
  - constructor.
    + unfold val1, is_ceil. simpl. lra.
    + constructor.
      * unfold val2, is_ceil. simpl. lra.
      * constructor.
        -- unfold val3, is_ceil. simpl. lra.
        -- constructor.
           ++ unfold val4, is_ceil. simpl. lra.
           ++ constructor.
              ** unfold val5. apply is_ceil_IZR.
              ** constructor.
                 --- unfold val6, is_ceil. simpl. lra.
                 --- constructor.
                     +++ unfold val7, is_ceil. simpl. lra.
                     +++ constructor.
                         *** unfold val8, is_ceil. simpl. lra.
                         *** constructor.
                             ---- unfold val9, is_ceil. simpl. lra.
                             ---- constructor.
  - simpl. reflexivity.
Qed.