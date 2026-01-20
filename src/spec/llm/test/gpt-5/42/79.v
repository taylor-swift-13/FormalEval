Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec
    [0.5%R; 88.08080880531568%R; -21.596861567647125%R; 0.14907947235135702%R; -59.15962684129501%R; -0.6821906440453559%R; -0.6752788781109065%R; -4.166307314246723%R; 0.14907947235135702%R]
    [0.5%R + 1%R; 88.08080880531568%R + 1%R; -21.596861567647125%R + 1%R; 0.14907947235135702%R + 1%R; -59.15962684129501%R + 1%R; -0.6821906440453559%R + 1%R; -0.6752788781109065%R + 1%R; -4.166307314246723%R + 1%R; 0.14907947235135702%R + 1%R].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.