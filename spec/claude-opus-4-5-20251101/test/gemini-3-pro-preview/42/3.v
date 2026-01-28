Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (result : list Z) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list: incr_list_spec [5%Z; 2%Z; 5%Z; 2%Z; 3%Z; 3%Z; 9%Z; 0%Z; 123%Z] [6%Z; 3%Z; 6%Z; 3%Z; 4%Z; 4%Z; 10%Z; 1%Z; 124%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.