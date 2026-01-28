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

Lemma is_ceil_neg2_neg25 : is_ceil (-2.5091429749847305) (-2)%Z.
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

Lemma is_ceil_3_29 : is_ceil 2.9 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_0_neg08 : is_ceil (-0.8413477856752207) 0%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg2_neg25_2 : is_ceil (-2.5091429749847305) (-2)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_4_35 : is_ceil 3.499530218204873 4%Z.
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

Lemma is_ceil_4_37 : is_ceil 3.729477873601854 4%Z.
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
  problem_133_spec [0.1; -2.5091429749847305; 1.5; 2.9; -0.8413477856752207; -2.5091429749847305; 3.499530218204873; 3.2; 3.729477873601854; 6.7] 119%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; (-2)%Z; 2%Z; 3%Z; 0%Z; (-2)%Z; 4%Z; 4%Z; 4%Z; 7%Z].
  split.
  - constructor.
    + apply is_ceil_1_01.
    + constructor.
      * apply is_ceil_neg2_neg25.
      * constructor.
        -- apply is_ceil_2_15.
        -- constructor.
           ++ apply is_ceil_3_29.
           ++ constructor.
              ** apply is_ceil_0_neg08.
              ** constructor.
                 --- apply is_ceil_neg2_neg25_2.
                 --- constructor.
                     +++ apply is_ceil_4_35.
                     +++ constructor.
                         *** apply is_ceil_4_32.
                         *** constructor.
                             ---- apply is_ceil_4_37.
                             ---- constructor.
                                  ++++ apply is_ceil_7_67.
                                  ++++ constructor.
  - simpl.
    reflexivity.
Qed.