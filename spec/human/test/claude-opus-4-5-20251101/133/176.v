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

Lemma is_ceil_0_1 : is_ceil 0.1 1%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_1_5 : is_ceil 1.5 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_4_716809497407311 : is_ceil (-4.716809497407311) (-4)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_2_9 : is_ceil 2.9 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_4_129563514953585 : is_ceil 4.129563514953585 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_4_967726321372912 : is_ceil 4.967726321372912 5%Z.
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

Lemma is_ceil_6_7 : is_ceil 6.7 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [0.1; 1.5; -4.716809497407311; 2.9; 4.129563514953585; 4.967726321372912; 4.6; 5.1; 6.7; 4.6] 215%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; 2%Z; (-4)%Z; 3%Z; 5%Z; 5%Z; 5%Z; 6%Z; 7%Z; 5%Z].
  split.
  - constructor.
    + apply is_ceil_0_1.
    + constructor.
      * apply is_ceil_1_5.
      * constructor.
        -- apply is_ceil_neg_4_716809497407311.
        -- constructor.
           ++ apply is_ceil_2_9.
           ++ constructor.
              ** apply is_ceil_4_129563514953585.
              ** constructor.
                 --- apply is_ceil_4_967726321372912.
                 --- constructor.
                     +++ apply is_ceil_4_6.
                     +++ constructor.
                         *** apply is_ceil_5_1.
                         *** constructor.
                             ---- apply is_ceil_6_7.
                             ---- constructor.
                                  ++++ apply is_ceil_4_6.
                                  ++++ constructor.
  - simpl.
    reflexivity.
Qed.