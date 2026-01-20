
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition ordering (p1 p2 : nat * nat) : Prop :=
  let (r1, c1) := p1 in
  let (r2, c2) := p2 in
  (r1 < r2)%nat \/ (r1 = r2 /\ c1 > c2)%nat.

Definition get_row_spec (lst : list (list Z)) (x : Z) (res : list (nat * nat)) : Prop :=
  (forall r c, In (r, c) res <-> 
     exists row, nth_error lst r = Some row /\ nth_error row c = Some x) /\
  Sorted ordering res.
