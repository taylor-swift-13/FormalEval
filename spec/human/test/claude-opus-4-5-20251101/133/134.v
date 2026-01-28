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

Lemma is_ceil_0_1_1 : is_ceil (1/10) 1%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_1_5_2 : is_ceil (3/2) 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_4_716_neg4 : is_ceil (-4716809497407311/1000000000000000) (-4)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_2_9_3 : is_ceil (29/10) 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_2_4 : is_ceil (16/5) 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_4_967_5 : is_ceil (4967726321372912/1000000000000000) 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_4_6_5 : is_ceil (23/5) 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_5_1_6 : is_ceil (51/10) 6%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_6_7_7 : is_ceil (67/10) 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [1/10; 3/2; -4716809497407311/1000000000000000; 29/10; 16/5; 4967726321372912/1000000000000000; 23/5; 51/10; 67/10] 181%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; 2%Z; (-4)%Z; 3%Z; 4%Z; 5%Z; 5%Z; 6%Z; 7%Z].
  split.
  - constructor.
    + apply is_ceil_0_1_1.
    + constructor.
      * apply is_ceil_1_5_2.
      * constructor.
        -- apply is_ceil_neg_4_716_neg4.
        -- constructor.
           ++ apply is_ceil_2_9_3.
           ++ constructor.
              ** apply is_ceil_3_2_4.
              ** constructor.
                 --- apply is_ceil_4_967_5.
                 --- constructor.
                     +++ apply is_ceil_4_6_5.
                     +++ constructor.
                         *** apply is_ceil_5_1_6.
                         *** constructor.
                             ---- apply is_ceil_6_7_7.
                             ---- constructor.
  - simpl.
    reflexivity.
Qed.