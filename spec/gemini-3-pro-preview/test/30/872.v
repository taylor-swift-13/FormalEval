Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example test_get_positive : get_positive_spec 
  [5.803598881698951; 25.221353337136023; -2.25; 8.193677988449515; -2.25] 
  [5.803598881698951; 25.221353337136023; 8.193677988449515].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat match goal with
  | |- context [if Rlt_dec 0 ?x then _ else _] =>
      destruct (Rlt_dec 0 x); try (exfalso; lra)
  end.
  reflexivity.
Qed.