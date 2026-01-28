Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list bool) : Prop := True.

Definition problem_52_spec (l : list bool) (t : Z) (output : bool) : Prop :=
  (Z.of_nat (length l) < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [false; true; false] 4%Z true.
Proof.
  unfold problem_52_spec.
  split.
  - intros _. reflexivity.
  - intros _. simpl. lia.
Qed.