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

Lemma is_ceil_2034150193392351 : is_ceil 2.034150193392351 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_4 : is_ceil 3.4 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_1_1237040199009254 : is_ceil 1.1237040199009254 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_2_3744170907243327 : is_ceil (-2.3744170907243327) (-2)%Z.
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

Example test_problem_133 :
  problem_133_spec [IZR 1; IZR 6; IZR 3; IZR 2; 2.034150193392351; 3.4; 1.1237040199009254; -2.3744170907243327; 0.5; IZR 6] 120%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; 6%Z; 3%Z; 2%Z; 3%Z; 4%Z; 2%Z; (-2)%Z; 1%Z; 6%Z].
  split.
  - constructor.
    + apply is_ceil_IZR.
    + constructor.
      * apply is_ceil_IZR.
      * constructor.
        -- apply is_ceil_IZR.
        -- constructor.
           ++ apply is_ceil_IZR.
           ++ constructor.
              ** apply is_ceil_2034150193392351.
              ** constructor.
                 --- apply is_ceil_3_4.
                 --- constructor.
                     +++ apply is_ceil_1_1237040199009254.
                     +++ constructor.
                         *** apply is_ceil_neg_2_3744170907243327.
                         *** constructor.
                             ---- apply is_ceil_0_5.
                             ---- constructor.
                                  ++++ apply is_ceil_IZR.
                                  ++++ constructor.
  - simpl.
    reflexivity.
Qed.