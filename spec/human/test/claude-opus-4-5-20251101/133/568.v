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

Lemma is_ceil_34_10 : is_ceil (34 / 10) 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_809_100 : is_ceil (-(809 / 100)) (-8)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_46_10 : is_ceil (-(46 / 10)) (-4)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_51_10 : is_ceil (51 / 10) 6%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [IZR 1; IZR (-1); IZR 2; 34 / 10; -(809 / 100); -(46 / 10); 51 / 10; IZR 6; IZR 6; -(809 / 100)] 274%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; (-1)%Z; 2%Z; 4%Z; (-8)%Z; (-4)%Z; 6%Z; 6%Z; 6%Z; (-8)%Z].
  split.
  - constructor.
    + apply is_ceil_IZR.
    + constructor.
      * apply is_ceil_IZR.
      * constructor.
        -- apply is_ceil_IZR.
        -- constructor.
           ++ apply is_ceil_34_10.
           ++ constructor.
              ** apply is_ceil_neg_809_100.
              ** constructor.
                 --- apply is_ceil_neg_46_10.
                 --- constructor.
                     +++ apply is_ceil_51_10.
                     +++ constructor.
                         *** apply is_ceil_IZR.
                         *** constructor.
                             ---- apply is_ceil_IZR.
                             ---- constructor.
                                  ++++ apply is_ceil_neg_809_100.
                                  ++++ constructor.
  - simpl.
    reflexivity.
Qed.