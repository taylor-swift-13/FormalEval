Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list R) : Prop := True.

Definition problem_52_spec (l : list R) (t : R) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [3.5; 2.6445924145352944; 2.2; 1.1] 3 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* The hypothesis H says all elements are < 3. We find a counterexample 3.5 in the list. *)
    assert (HIn : In 3.5 [3.5; 2.6445924145352944; 2.2; 1.1]).
    { simpl. left. reflexivity. }
    specialize (H 3.5 HIn).
    lra.
  - (* Right to Left implication *)
    intros H.
    (* H is false = true, which is a contradiction *)
    discriminate.
Qed.