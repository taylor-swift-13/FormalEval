Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope R_scope.

(* z is the ceiling of x: IZR z - 1 < x <= IZR z *)
Definition is_ceil (x : R) (z : Z) : Prop :=
  (IZR z - 1 < x) /\ (x <= IZR z).

(* Precondition *)
Definition problem_133_pre (lst : list R) : Prop := True.

(* Specification *)
Definition problem_133_spec (lst : list R) (s : Z) : Prop :=
  exists zs : list Z,
    Forall2 is_ceil lst zs /\
    s = fold_right Z.add 0%Z (map (fun z => Z.mul z z) zs).

Example test_case_problem_133 : problem_133_spec [IZR 1; IZR 2; IZR 3] 14%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; 2%Z; 3%Z].
  split.
  - (* Prove Forall2 is_ceil ... *)
    apply Forall2_cons.
    + (* is_ceil (IZR 1) 1 *)
      unfold is_ceil. split.
      * apply Rlt_minus_l.
        apply Rlt_plus_1.
      * apply Rle_refl.
    + apply Forall2_cons.
      * (* is_ceil (IZR 2) 2 *)
        unfold is_ceil. split.
        -- apply Rlt_minus_l.
           apply Rlt_plus_1.
        -- apply Rle_refl.
      * apply Forall2_cons.
        -- (* is_ceil (IZR 3) 3 *)
           unfold is_ceil. split.
           ++ apply Rlt_minus_l.
              apply Rlt_plus_1.
           ++ apply Rle_refl.
        -- apply Forall2_nil.
  - (* Sum calculation *)
    simpl. reflexivity.
Qed.