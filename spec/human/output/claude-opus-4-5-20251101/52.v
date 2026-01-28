Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_below_threshold_1 : problem_52_spec [1%Z; 2%Z; 4%Z; 10%Z] 100%Z true.
Proof.
  unfold problem_52_spec.
  split.
  - intros H. reflexivity.
  - intros H x Hx.
    simpl in Hx.
    destruct Hx as [Hx | [Hx | [Hx | [Hx | Hx]]]].
    + subst x. lia.
    + subst x. lia.
    + subst x. lia.
    + subst x. lia.
    + contradiction.
Qed.