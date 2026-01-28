Require Import Coq.Lists.List.
Require Import Coq.Floats.Floats.
Import ListNotations.
Open Scope float_scope.
Delimit Scope float_scope with R.

Definition incr_list_spec (l : list float) (res : list float) : Prop :=
  res = map (fun x => x + 1.0) l.

Example test_incr_list : incr_list_spec [3.5652526206208957%R; 3.7%R; 8.9%R; 0.5%R; 8.9%R] [4.565252620620896%R; 4.7%R; 9.9%R; 1.5%R; 9.9%R].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.