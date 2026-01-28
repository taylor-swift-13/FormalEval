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

Lemma is_ceil_neg2_5 : is_ceil (-2.5) (-2)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_0_5 : is_ceil 0.5 1%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_1_31 : is_ceil 1.3122633441453049 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg1_1 : is_ceil (-1.1) (-1)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg1_82 : is_ceil (-1.820012478772272) (-1)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [-2.5; 0.5; 1.3122633441453049; -1.1; -1.820012478772272; -1.1; -2.5] 16%Z.
Proof.
  unfold problem_133_spec.
  exists [(-2)%Z; 1%Z; 2%Z; (-1)%Z; (-1)%Z; (-1)%Z; (-2)%Z].
  split.
  - constructor.
    + apply is_ceil_neg2_5.
    + constructor.
      * apply is_ceil_0_5.
      * constructor.
        -- apply is_ceil_1_31.
        -- constructor.
           ++ apply is_ceil_neg1_1.
           ++ constructor.
              ** apply is_ceil_neg1_82.
              ** constructor.
                 --- apply is_ceil_neg1_1.
                 --- constructor.
                     +++ apply is_ceil_neg2_5.
                     +++ constructor.
  - simpl.
    reflexivity.
Qed.