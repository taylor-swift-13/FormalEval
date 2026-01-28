Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [10; 20; -30; 40; -50; 20] 9 false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    (* The hypothesis H says all elements are < 9. 
       We instantiate it with 10, which is in the list, to derive a contradiction. *)
    specialize (H 10).
    assert (In 10 [10; 20; -30; 40; -50; 20]).
    { simpl. left. reflexivity. }
    apply H in H0.
    lia.
  - intros H.
    (* false = true is False, so this direction is trivial by discrimination *)
    discriminate.
Qed.