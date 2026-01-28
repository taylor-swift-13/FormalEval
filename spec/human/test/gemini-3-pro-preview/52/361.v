Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [1000; 500; 250; 125; 62; 30; 500] 2001 true.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    reflexivity.
  - intros _ x HIn.
    simpl in HIn.
    destruct HIn as [H | [H | [H | [H | [H | [H | [H | H]]]]]]].
    + rewrite <- H.
      lia.
    + rewrite <- H.
      lia.
    + rewrite <- H.
      lia.
    + rewrite <- H.
      lia.
    + rewrite <- H.
      lia.
    + rewrite <- H.
      lia.
    + rewrite <- H.
      lia.
    + contradiction.
Qed.