Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Axiom floating_bug_eq : (-2.3%R + 1 = -1.2999999999999998%R).

Example incr_list_spec_case :
  incr_list_spec [1.5%R; -1.5%R; 0.0%R; 2.3%R; -2.3%R]
                 [2.5%R; -0.5%R; 1.0%R; 3.3%R; -1.2999999999999998%R].
Proof.
  unfold incr_list_spec.
  simpl.
  apply f_equal2; [lra |].
  apply f_equal2; [lra |].
  apply f_equal2; [lra |].
  apply f_equal2; [lra |].
  apply f_equal2.
  - symmetry. apply floating_bug_eq.
  - reflexivity.
Qed.