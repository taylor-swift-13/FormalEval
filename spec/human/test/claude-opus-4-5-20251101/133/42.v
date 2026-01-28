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

Lemma is_ceil_1_of_half : is_ceil (1/2) 1%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_4_of_3_3 : is_ceil (33/10) 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_1_of_0_565 : is_ceil (5651200929607817 / 10000000000000000) 1%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [1/2; 33/10; 5651200929607817 / 10000000000000000] 18%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; 4%Z; 1%Z].
  split.
  - constructor.
    + apply is_ceil_1_of_half.
    + constructor.
      * apply is_ceil_4_of_3_3.
      * constructor.
        -- apply is_ceil_1_of_0_565.
        -- constructor.
  - simpl.
    reflexivity.
Qed.