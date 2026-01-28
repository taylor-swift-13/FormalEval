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

Lemma is_ceil_4_2 : is_ceil (4 + 2/10) 5.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_1_5 : is_ceil (-(1 + 5/10)) (-1).
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_2_7 : is_ceil (-(2 + 7/10)) (-2).
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_6 : is_ceil (3 + 6/10) 4.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_7_1 : is_ceil (7 + 1/10) 8.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_6_5 : is_ceil (-(6 + 5/10)) (-6).
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [4 + 2/10; IZR 0; -(1 + 5/10); -(2 + 7/10); 3 + 6/10; 7 + 1/10; IZR 1; -(6 + 5/10); -(1 + 5/10); -(1 + 5/10)] 149%Z.
Proof.
  unfold problem_133_spec.
  exists [5%Z; 0%Z; (-1)%Z; (-2)%Z; 4%Z; 8%Z; 1%Z; (-6)%Z; (-1)%Z; (-1)%Z].
  split.
  - constructor.
    + apply is_ceil_4_2.
    + constructor.
      * apply is_ceil_IZR.
      * constructor.
        -- apply is_ceil_neg_1_5.
        -- constructor.
           ++ apply is_ceil_neg_2_7.
           ++ constructor.
              ** apply is_ceil_3_6.
              ** constructor.
                 --- apply is_ceil_7_1.
                 --- constructor.
                     +++ apply is_ceil_IZR.
                     +++ constructor.
                         *** apply is_ceil_neg_6_5.
                         *** constructor.
                             ---- apply is_ceil_neg_1_5.
                             ---- constructor.
                                  ++++ apply is_ceil_neg_1_5.
                                  ++++ constructor.
  - simpl.
    reflexivity.
Qed.