Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [2000000; 10000000; 9000000; 10; 8000000; 7000000; 6000000; 2000000; 7000000] 10000000 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* The hypothesis H says all elements are < 10000000. 
       We show a contradiction by exhibiting 10000000 in the list. *)
    specialize (H 10000000).
    assert (In 10000000 [2000000; 10000000; 9000000; 10; 8000000; 7000000; 6000000; 2000000; 7000000]) as HIn.
    { simpl. right. left. reflexivity. }
    apply H in HIn.
    lia.
  - (* Right to Left implication *)
    intros H.
    discriminate H.
Qed.