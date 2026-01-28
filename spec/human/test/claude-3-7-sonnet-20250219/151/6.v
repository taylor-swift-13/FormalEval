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

Example test_nonempty_list :
  problem_151_spec [0; 3; 5] 34%Z.
Proof.
  unfold problem_151_spec.
  simpl.
  (* Evaluate the fold step by step *)
  (* acc = 0, h = 0: (0 ≤ 0) && odd(0) = true && false = false -> acc = 0 *)
  (* acc = 0, h = 3: (0 ≤ 3) && odd(3) = true && true = true -> acc = 0 + 3*3 = 9 *)
  (* acc = 9, h = 5: (0 ≤ 5) && odd(5) = true && true = true -> acc = 9 + 5*5 = 34 *)
  reflexivity.
Qed.