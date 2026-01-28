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

Lemma is_ceil_1_01 : is_ceil 0.1 1%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_6_55 : is_ceil 5.5 6%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_7_6851 : is_ceil 6.851261387881998 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_4_32 : is_ceil 3.2 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_5_46 : is_ceil 4.6 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_2493 : is_ceil 2.4936669865395658 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_6_51 : is_ceil 5.1 6%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_7_67 : is_ceil 6.7 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [0.1; 5.5; 6.851261387881998; 3.2; 4.6; 2.4936669865395658; 5.1; 6.7; 6.7] 270%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; 6%Z; 7%Z; 4%Z; 5%Z; 3%Z; 6%Z; 7%Z; 7%Z].
  split.
  - constructor.
    + apply is_ceil_1_01.
    + constructor.
      * apply is_ceil_6_55.
      * constructor.
        -- apply is_ceil_7_6851.
        -- constructor.
           ++ apply is_ceil_4_32.
           ++ constructor.
              ** apply is_ceil_5_46.
              ** constructor.
                 --- apply is_ceil_3_2493.
                 --- constructor.
                     +++ apply is_ceil_6_51.
                     +++ constructor.
                         *** apply is_ceil_7_67.
                         *** constructor.
                             ---- apply is_ceil_7_67.
                             ---- constructor.
  - simpl.
    reflexivity.
Qed.