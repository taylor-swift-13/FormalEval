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

Lemma is_ceil_6_508 : is_ceil 5.080474606366394 6%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_5_423 : is_ceil 4.234081562814888 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_7_685 : is_ceil 6.851261387881998 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_9_852 : is_ceil 8.527593815012729 9%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_2_15 : is_ceil 1.5 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [0.1; 5.080474606366394; 4.234081562814888; 6.851261387881998; 8.527593815012729; 4.234081562814888; 1.5; 4.234081562814888] 246%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; 6%Z; 5%Z; 7%Z; 9%Z; 5%Z; 2%Z; 5%Z].
  split.
  - constructor.
    + apply is_ceil_1_01.
    + constructor.
      * apply is_ceil_6_508.
      * constructor.
        -- apply is_ceil_5_423.
        -- constructor.
           ++ apply is_ceil_7_685.
           ++ constructor.
              ** apply is_ceil_9_852.
              ** constructor.
                 --- apply is_ceil_5_423.
                 --- constructor.
                     +++ apply is_ceil_2_15.
                     +++ constructor.
                         *** apply is_ceil_5_423.
                         *** constructor.
  - simpl.
    reflexivity.
Qed.