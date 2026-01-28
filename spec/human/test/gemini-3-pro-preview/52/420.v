Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list R) : Prop := True.

Definition problem_52_spec (l : list R) (t : R) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [0.2; 62.5; -63.579573934400166; 0.5; 98.82739614126038; -0.28791951724548404; -50.78504214587984; 58.062454697705476; 55.110190228263775; 10.520189946545017] 0 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* We instantiate the universal quantifier with a counter-example from the list *)
    assert (HIn : In 0.2 [0.2; 62.5; -63.579573934400166; 0.5; 98.82739614126038; -0.28791951724548404; -50.78504214587984; 58.062454697705476; 55.110190228263775; 10.520189946545017]).
    { simpl. left. reflexivity. }
    specialize (H 0.2 HIn).
    lra.
  - (* Right to Left implication *)
    intros H.
    discriminate.
Qed.