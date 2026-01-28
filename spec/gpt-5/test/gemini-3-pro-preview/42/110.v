Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example test_incr_list_large : incr_list_spec [10000; 20000; 30000; 40000; 50000; 60000; 70000; 80000; 90000; 100000] [10001; 20001; 30001; 40001; 50001; 60001; 70001; 80001; 90001; 100001].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.