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

Lemma is_ceil_1_1 : is_ceil (1 + /10) 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Lemma is_ceil_2_5 : is_ceil (2 + /2) 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Lemma is_ceil_neg_3_7 : is_ceil (-(3 + 7/10)) (-3)%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Lemma is_ceil_neg_4_716 : is_ceil (-4716809497407311/1000000000000000) (-4)%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Lemma is_ceil_5_2 : is_ceil (5 + /5) 6%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Example test_problem_133 :
  problem_133_spec [1 + /10; 2 + /2; -(3 + 7/10); -4716809497407311/1000000000000000; IZR 5; 5 + /5; IZR (-3); 5 + /5] 144%Z.
Proof.
  unfold problem_133_spec.
  exists [2%Z; 3%Z; (-3)%Z; (-4)%Z; 5%Z; 6%Z; (-3)%Z; 6%Z].
  split.
  - constructor.
    + apply is_ceil_1_1.
    + constructor.
      * apply is_ceil_2_5.
      * constructor.
        -- apply is_ceil_neg_3_7.
        -- constructor.
           ++ apply is_ceil_neg_4_716.
           ++ constructor.
              ** apply is_ceil_IZR.
              ** constructor.
                 --- apply is_ceil_5_2.
                 --- constructor.
                     +++ apply is_ceil_IZR.
                     +++ constructor.
                         *** apply is_ceil_5_2.
                         *** constructor.
  - simpl.
    reflexivity.
Qed.