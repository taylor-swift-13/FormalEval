Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Reals.
Import ListNotations.
Open Scope bool_scope.
Open Scope Z_scope.
Open Scope R_scope.

Inductive Num : Set :=
| NInt : Z -> Num
| NReal : R -> Num.

Definition problem_151_pre (l : list Num) : Prop := True.

Definition problem_151_spec (l : list Num) (res : Z) : Prop :=
  res = fold_left (fun acc h =>
                     match h with
                     | NInt z =>
                         if (Z.leb 0 z) && (Z.odd z)
                         then Z.add acc (Z.mul z z)
                         else acc
                     | NReal _ => acc
                     end) l 0%Z.

Example problem_151_test_case :
  problem_151_spec
    [NInt 1%Z; NInt (-3)%Z; NReal (-12.8%R); NInt (-5)%Z; NReal (10.5%R); NInt 1%Z; NReal (8.3%R); NReal (9.9%R); NReal (2.5%R); NReal (2.5%R); NInt 1%Z; NReal (4.3534083434836495%R); NInt 1%Z]
    4%Z.
Proof.
  unfold problem_151_spec.
  simpl.
  reflexivity.
Qed.