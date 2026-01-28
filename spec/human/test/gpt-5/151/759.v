Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope bool_scope.
Open Scope Z_scope.

Definition problem_151_pre (l : list Z) : Prop := True.

Definition problem_151_spec (l : list Z) (res : Z) : Prop :=
  res = fold_left (fun acc h => if (Z.leb 0 h) && (Z.odd h)
                          then Z.add acc (Z.mul h h)
                          else acc) l 0.

Example problem_151_test_case :
  problem_151_spec [0%Z; (* 2.5%R; 3.7%R; *) -5%Z; -13%Z; (* 10.5%R; -12.8%R; *) -14%Z; (* 10.5%R; -15.3%R; *) -16%Z; -18%Z; 19%Z; (* 20.2%R; 21.9%R; -23.8%R; *) 24%Z; 6%Z; 25%Z; 26%Z; (* 2.5%R; 2.206800561418771%R; 19.2%R; *) -28%Z; -29%Z; -28%Z; -18%Z] 986%Z.
Proof.
  unfold problem_151_spec.
  simpl.
  reflexivity.
Qed.