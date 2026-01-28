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

Lemma is_ceil_2_25 : is_ceil (1 + 1/10) 2.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_25 : is_ceil (2 + 1/2) 3.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg4_46 : is_ceil (-(4 + 6/10)) (-4).
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_1_frac : is_ceil (6212597321029525 / 10000000000000000) 1.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_6_52 : is_ceil (5 + 2/10) 6.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [1 + 1/10; 2 + 1/2; -(4 + 6/10); 6212597321029525 / 10000000000000000; 5 + 2/10; IZR 6; 5 + 2/10] 138%Z.
Proof.
  unfold problem_133_spec.
  exists [2%Z; 3%Z; (-4)%Z; 1%Z; 6%Z; 6%Z; 6%Z].
  split.
  - constructor.
    + apply is_ceil_2_25.
    + constructor.
      * apply is_ceil_3_25.
      * constructor.
        -- apply is_ceil_neg4_46.
        -- constructor.
           ++ apply is_ceil_1_frac.
           ++ constructor.
              ** apply is_ceil_6_52.
              ** constructor.
                 --- apply is_ceil_IZR.
                 --- constructor.
                     +++ apply is_ceil_6_52.
                     +++ constructor.
  - simpl.
    reflexivity.
Qed.