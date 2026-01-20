Require Import Coq.Lists.List.
Import ListNotations.

Definition solution (l : list bool) : bool :=
  forallb (fun x => x) l.

Example test_case : solution [true; true; true; false; true; true] = false.
Proof.
  simpl. reflexivity.
Qed.