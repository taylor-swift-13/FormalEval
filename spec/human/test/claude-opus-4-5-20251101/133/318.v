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

Lemma is_ceil_2_of_1_5 : is_ceil (3/2) 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_2_of_1_1 : is_ceil (11/10) 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_4_of_3_2 : is_ceil (16/5) 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_5_of_4_234 : is_ceil (4234081562814888 / 1000000000000000) 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_7_of_6_851 : is_ceil (6851261387881998 / 1000000000000000) 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_7_of_6_7 : is_ceil (67/10) 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [3/2; 11/10; 16/5; 4234081562814888/1000000000000000; 6851261387881998/1000000000000000; 67/10] 147%Z.
Proof.
  unfold problem_133_spec.
  exists [2%Z; 2%Z; 4%Z; 5%Z; 7%Z; 7%Z].
  split.
  - constructor.
    + apply is_ceil_2_of_1_5.
    + constructor.
      * apply is_ceil_2_of_1_1.
      * constructor.
        -- apply is_ceil_4_of_3_2.
        -- constructor.
           ++ apply is_ceil_5_of_4_234.
           ++ constructor.
              ** apply is_ceil_7_of_6_851.
              ** constructor.
                 --- apply is_ceil_7_of_6_7.
                 --- constructor.
  - simpl.
    reflexivity.
Qed.