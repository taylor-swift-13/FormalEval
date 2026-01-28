Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [10; 20; 1; 40; -50] 15 false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    (* The hypothesis implies all elements are < 15. We show a counter-example (20). *)
    specialize (H 20).
    simpl in H.
    assert (20 < 15).
    { 
      apply H. 
      (* Prove In 20 [10; 20; 1; 40; -50] *)
      right. left. reflexivity. 
    }
    lia.
  - intros H.
    (* false = true is a contradiction *)
    discriminate.
Qed.