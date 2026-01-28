Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [2000000; 8000001; 10000000; 9000000; 10; 8000000; 7000000; 2000000; 6000000; 10; 2000000; 2000000] 10000001 true.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    reflexivity.
  - intros _ x HIn.
    simpl in HIn.
    repeat (destruct HIn as [H | HIn]; [ rewrite <- H; lia | ]).
    contradiction.
Qed.