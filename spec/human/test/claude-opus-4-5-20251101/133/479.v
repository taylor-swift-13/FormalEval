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

Lemma is_ceil_4_5 : is_ceil 4.5 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_2_034 : is_ceil 2.034150193392351 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
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

Lemma is_ceil_2_9 : is_ceil 2.9 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_2 : is_ceil 3.2 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_287 : is_ceil 3.287852215132159 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_6_240 : is_ceil 6.240762858871131 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [4.5; 2.034150193392351; 0.1; 1.5; 2.9; 3.2; 3.287852215132159; 6.240762858871131; 3.287852215132159; 4.5] 170%Z.
Proof.
  unfold problem_133_spec.
  exists [5%Z; 3%Z; 1%Z; 2%Z; 3%Z; 4%Z; 4%Z; 7%Z; 4%Z; 5%Z].
  split.
  - constructor.
    + apply is_ceil_4_5.
    + constructor.
      * apply is_ceil_2_034.
      * constructor.
        -- apply is_ceil_0_1.
        -- constructor.
           ++ apply is_ceil_1_5.
           ++ constructor.
              ** apply is_ceil_2_9.
              ** constructor.
                 --- apply is_ceil_3_2.
                 --- constructor.
                     +++ apply is_ceil_3_287.
                     +++ constructor.
                         *** apply is_ceil_6_240.
                         *** constructor.
                             ---- apply is_ceil_3_287.
                             ---- constructor.
                                  ++++ apply is_ceil_4_5.
                                  ++++ constructor.
  - simpl.
    reflexivity.
Qed.