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

Lemma is_ceil_2_5 : is_ceil 2.5 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg3_7 : is_ceil (-3.7) (-3)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_074 : is_ceil 3.074745760163279 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_5_570 : is_ceil 5.570054272140174 6%Z.
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

Lemma is_ceil_4_532 : is_ceil 4.532971210865655 5%Z.
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

Example test_problem_133 :
  problem_133_spec [(-1.1); 2.5; (-3.7); 3.074745760163279; 5.570054272140174; IZR 6; 5.1; 4.532971210865655; 4.6] 193%Z.
Proof.
  unfold problem_133_spec.
  exists [(-1)%Z; 3%Z; (-3)%Z; 4%Z; 6%Z; 6%Z; 6%Z; 5%Z; 5%Z].
  split.
  - constructor.
    + apply is_ceil_neg1_1.
    + constructor.
      * apply is_ceil_2_5.
      * constructor.
        -- apply is_ceil_neg3_7.
        -- constructor.
           ++ apply is_ceil_3_074.
           ++ constructor.
              ** apply is_ceil_5_570.
              ** constructor.
                 --- apply is_ceil_IZR.
                 --- constructor.
                     +++ apply is_ceil_5_1.
                     +++ constructor.
                         *** apply is_ceil_4_532.
                         *** constructor.
                             ---- apply is_ceil_4_6.
                             ---- constructor.
  - simpl.
    reflexivity.
Qed.