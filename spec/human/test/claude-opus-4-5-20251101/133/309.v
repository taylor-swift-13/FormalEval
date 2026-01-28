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

Lemma is_ceil_01_1 : is_ceil 0.1 1%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg25_neg2 : is_ceil (-2.5091429749847305) (-2)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_15_2 : is_ceil 1.5 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_29_3 : is_ceil 2.9 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_32_4 : is_ceil 3.2 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_4234_5 : is_ceil 4.234081562814888 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3729_4 : is_ceil 3.729477873601854 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_67_7 : is_ceil 6.7 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [0.1; -2.5091429749847305; 1.5; 2.9; -2.5091429749847305; 3.2; 4.234081562814888; 3.729477873601854; 6.7] 128%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; (-2)%Z; 2%Z; 3%Z; (-2)%Z; 4%Z; 5%Z; 4%Z; 7%Z].
  split.
  - constructor.
    + apply is_ceil_01_1.
    + constructor.
      * apply is_ceil_neg25_neg2.
      * constructor.
        -- apply is_ceil_15_2.
        -- constructor.
           ++ apply is_ceil_29_3.
           ++ constructor.
              ** apply is_ceil_neg25_neg2.
              ** constructor.
                 --- apply is_ceil_32_4.
                 --- constructor.
                     +++ apply is_ceil_4234_5.
                     +++ constructor.
                         *** apply is_ceil_3729_4.
                         *** constructor.
                             ---- apply is_ceil_67_7.
                             ---- constructor.
  - simpl.
    reflexivity.
Qed.