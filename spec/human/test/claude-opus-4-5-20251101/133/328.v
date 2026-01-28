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

Lemma is_ceil_2_4 : is_ceil (2.4) 3%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_4_2 : is_ceil (4.2) 5%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_neg_1_5 : is_ceil (-1.5) (-1)%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_neg_2_7 : is_ceil (-2.7) (-2)%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_neg_4_276 : is_ceil (-4.276480747131856) (-4)%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_7_1 : is_ceil (7.1) 8%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_neg_6_5 : is_ceil (-6.5) (-6)%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_neg_1_98 : is_ceil (-1.9831292900001547) (-1)%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Example test_problem_133 :
  problem_133_spec [2.4; 4.2; IZR 0; -1.5; -2.7; -4.276480747131856; 7.1; -6.5; -1.5; -1.9831292900001547; -2.7] 161%Z.
Proof.
  unfold problem_133_spec.
  exists [3%Z; 5%Z; 0%Z; (-1)%Z; (-2)%Z; (-4)%Z; 8%Z; (-6)%Z; (-1)%Z; (-1)%Z; (-2)%Z].
  split.
  - constructor.
    + apply is_ceil_2_4.
    + constructor.
      * apply is_ceil_4_2.
      * constructor.
        -- apply is_ceil_IZR.
        -- constructor.
           ++ apply is_ceil_neg_1_5.
           ++ constructor.
              ** apply is_ceil_neg_2_7.
              ** constructor.
                 --- apply is_ceil_neg_4_276.
                 --- constructor.
                     +++ apply is_ceil_7_1.
                     +++ constructor.
                         *** apply is_ceil_neg_6_5.
                         *** constructor.
                             ---- apply is_ceil_neg_1_5.
                             ---- constructor.
                                  ++++ apply is_ceil_neg_1_98.
                                  ++++ constructor.
                                       **** apply is_ceil_neg_2_7.
                                       **** constructor.
  - simpl.
    reflexivity.
Qed.