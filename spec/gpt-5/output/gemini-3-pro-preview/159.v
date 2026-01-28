Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition eat_spec (number need remaining : Z) (res : list Z) : Prop :=
  0 <= number /\ number <= 1000 /\
  0 <= need /\ need <= 1000 /\
  0 <= remaining /\ remaining <= 1000 /\
  res =
    (if Z.leb need remaining
     then [number + need; remaining - need]
     else [number + remaining; 0]).

Example test_eat_case1: eat_spec 5 6 10 [11; 4].
Proof.
  unfold eat_spec.
  (* We use 'repeat split' to break down the conjunctions.
     Then we try 'lia' to solve the integer inequalities.
     Finally, we try 'simpl; reflexivity' to solve the list equality.
     Chaining with ';' ensures that if 'lia' solves all goals, the subsequent tactics are skipped, preventing "No such goal" errors. *)
  repeat split; try lia; try (simpl; reflexivity).
Qed.