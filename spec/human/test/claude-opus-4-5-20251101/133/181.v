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

Lemma is_ceil_4_164996313633066_5 : is_ceil 4.164996313633066 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_4_4 : is_ceil 3.4 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_5_1_6 : is_ceil 5.1 6%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [4.164996313633066; IZR 1; IZR 4; 3.4; 5.1; IZR 6; 3.4; IZR 4] 162%Z.
Proof.
  unfold problem_133_spec.
  exists [5%Z; 1%Z; 4%Z; 4%Z; 6%Z; 6%Z; 4%Z; 4%Z].
  split.
  - constructor.
    + apply is_ceil_4_164996313633066_5.
    + constructor.
      * apply is_ceil_IZR.
      * constructor.
        -- apply is_ceil_IZR.
        -- constructor.
           ++ apply is_ceil_3_4_4.
           ++ constructor.
              ** apply is_ceil_5_1_6.
              ** constructor.
                 --- apply is_ceil_IZR.
                 --- constructor.
                     +++ apply is_ceil_3_4_4.
                     +++ constructor.
                         *** apply is_ceil_IZR.
                         *** constructor.
  - simpl.
    reflexivity.
Qed.