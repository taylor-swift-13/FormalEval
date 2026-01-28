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

Lemma is_ceil_2_9_3 : is_ceil (29/10) 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_1_275713502619218_2 : is_ceil 1.275713502619218 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_975992715202202_4 : is_ceil 3.975992715202202 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_6_851261387881998_7 : is_ceil 6.851261387881998 7%Z.
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

Lemma is_ceil_3_172195971968054_4 : is_ceil 3.172195971968054 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [1/10; 3/2; 29/10; 1.275713502619218; 3.975992715202202; 6.851261387881998; 67/10; 3.172195971968054; 29/10; 29/10; 6.851261387881998] 215%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; 2%Z; 3%Z; 2%Z; 4%Z; 7%Z; 7%Z; 4%Z; 3%Z; 3%Z; 7%Z].
  split.
  - constructor.
    + apply is_ceil_0_1_1.
    + constructor.
      * apply is_ceil_1_5_2.
      * constructor.
        -- apply is_ceil_2_9_3.
        -- constructor.
           ++ apply is_ceil_1_275713502619218_2.
           ++ constructor.
              ** apply is_ceil_3_975992715202202_4.
              ** constructor.
                 --- apply is_ceil_6_851261387881998_7.
                 --- constructor.
                     +++ apply is_ceil_6_7_7.
                     +++ constructor.
                         *** apply is_ceil_3_172195971968054_4.
                         *** constructor.
                             ---- apply is_ceil_2_9_3.
                             ---- constructor.
                                  ++++ apply is_ceil_2_9_3.
                                  ++++ constructor.
                                       **** apply is_ceil_6_851261387881998_7.
                                       **** constructor.
  - simpl.
    reflexivity.
Qed.