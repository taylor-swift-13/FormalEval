Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

(* Test case: input = [[1%Z; 2%Z; 4%Z; 10%Z]; 100%Z], output = true *)
Example problem_52_example :
  problem_52_spec [1; 2; 4; 10] 100 true.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    reflexivity.
  - intros H x Hx.
    simpl in Hx.
    destruct Hx as [Hx | [Hx | [Hx | [Hx | Hx]]]];
    subst; try lia.
Qed.