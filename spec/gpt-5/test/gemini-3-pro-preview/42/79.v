Require Import Coq.Lists.List.
Require Import Coq.Floats.Floats.
Import ListNotations.

Open Scope float_scope.
Delimit Scope float_scope with R.

Definition incr_list_spec (l : list float) (res : list float) : Prop :=
  res = List.map (fun x => x + 1.0) l.

Example test_incr_list_float : incr_list_spec 
  [0.5%R; 88.08080880531568%R; -21.596861567647125%R; 0.14907947235135702%R; -59.15962684129501%R; -0.6821906440453559%R; -0.6752788781109065%R; -4.166307314246723%R; 0.14907947235135702%R] 
  [1.5%R; 89.08080880531568%R; -20.596861567647125%R; 1.149079472351357%R; -58.15962684129501%R; 0.3178093559546441%R; 0.3247211218890935%R; -3.1663073142467226%R; 1.149079472351357%R].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.