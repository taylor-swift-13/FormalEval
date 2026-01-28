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

Lemma is_ceil_24_3 : is_ceil (24/10) 3%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_42_5 : is_ceil (42/10) 5%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_0_0 : is_ceil 0 0%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_neg15_neg1 : is_ceil (-(15/10)) (-1)%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_neg27_neg2 : is_ceil (-(27/10)) (-2)%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_36_4 : is_ceil (36/10) 4%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_71_8 : is_ceil (71/10) 8%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_neg65_neg6 : is_ceil (-(65/10)) (-6)%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Example test_problem_133 :
  problem_133_spec [24/10; 42/10; 0; -(15/10); -(27/10); 36/10; 71/10; -(65/10)] 155%Z.
Proof.
  unfold problem_133_spec.
  exists [3%Z; 5%Z; 0%Z; (-1)%Z; (-2)%Z; 4%Z; 8%Z; (-6)%Z].
  split.
  - constructor.
    + apply is_ceil_24_3.
    + constructor.
      * apply is_ceil_42_5.
      * constructor.
        -- apply is_ceil_0_0.
        -- constructor.
           ++ apply is_ceil_neg15_neg1.
           ++ constructor.
              ** apply is_ceil_neg27_neg2.
              ** constructor.
                 --- apply is_ceil_36_4.
                 --- constructor.
                     +++ apply is_ceil_71_8.
                     +++ constructor.
                         *** apply is_ceil_neg65_neg6.
                         *** constructor.
  - simpl.
    reflexivity.
Qed.