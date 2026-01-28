Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `pairs_sum_to_zero` *)
Definition problem_43_pre (input : list Z) : Prop := True.

Definition problem_43_spec (input : list Z) (output : bool) : Prop :=
  (exists i j : nat,
    (i <> j)  /\
    (i < length input)%nat /\
    (j < length input)%nat /\
    (nth i input 0 + nth j input 0 = 0))
  <-> (output = true).

Example test_problem_43 : problem_43_spec [-3; 9; -1; 3; 2; 30] true.
Proof.
  unfold problem_43_spec.
  split.
  - (* Forward direction: (Exists ...) -> true = true *)
    intro H. reflexivity.
  - (* Backward direction: true = true -> Exists ... *)
    intro H.
    (* We need to provide witnesses i and j such that input[i] + input[j] = 0 *)
    (* In [-3; 9; -1; 3; 2; 30], indices 0 (-3) and 3 (3) sum to 0 *)
    exists 0%nat, 3%nat.
    split.
    + (* 0 <> 3 *)
      lia.
    + split.
      * (* 0 < length *)
        simpl. lia.
      * split.
        -- (* 3 < length *)
           simpl. lia.
        -- (* -3 + 3 = 0 *)
           simpl. reflexivity.
Qed.