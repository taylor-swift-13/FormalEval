Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [10000000; 9000000; 8000000; 2000; 6000000; 2000000] 10000000 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* The hypothesis H states that every element in the list is strictly less than 10000000.
       However, 10000000 is the first element of the list. *)
    assert (Contra : 10000000 < 10000000).
    { apply H. simpl. left. reflexivity. }
    lia.
  - (* Right to Left implication *)
    intros H.
    (* The hypothesis H is false = true, which is a contradiction. *)
    discriminate.
Qed.