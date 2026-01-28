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

Lemma is_ceil_2_of_1_1 : is_ceil (11/10) 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_of_2_5 : is_ceil (5/2) 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg4_of_neg4_6 : is_ceil (-23/5) (-4)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_1_of_0_62 : is_ceil (6212597321029525/10000000000000000) 1%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_6_of_5_2 : is_ceil (26/5) 6%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [11/10; 5/2; -23/5; 6212597321029525/10000000000000000; 26/5; IZR 6; 26/5; 26/5] 174%Z.
Proof.
  unfold problem_133_spec.
  exists [2%Z; 3%Z; (-4)%Z; 1%Z; 6%Z; 6%Z; 6%Z; 6%Z].
  split.
  - constructor.
    + apply is_ceil_2_of_1_1.
    + constructor.
      * apply is_ceil_3_of_2_5.
      * constructor.
        -- apply is_ceil_neg4_of_neg4_6.
        -- constructor.
           ++ apply is_ceil_1_of_0_62.
           ++ constructor.
              ** apply is_ceil_6_of_5_2.
              ** constructor.
                 --- apply is_ceil_IZR.
                 --- constructor.
                     +++ apply is_ceil_6_of_5_2.
                     +++ constructor.
                         *** apply is_ceil_6_of_5_2.
                         *** constructor.
  - simpl.
    reflexivity.
Qed.