Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [10; 20; 1; 40; 9; -50; -50] 499 true.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    reflexivity.
  - (* Right to Left implication *)
    intros _ x HIn.
    simpl in HIn.
    repeat (destruct HIn as [H | HIn]; [ rewrite <- H; lia | ]).
    contradiction.
Qed.