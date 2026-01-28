Require Import List ZArith Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_9_pre : Prop := True.

Definition problem_9_spec (input output : list Z) :=
  length output = length input /\
  forall i,
    (i < length output)%nat ->
    (forall j, (j <= i)%nat -> nth j input 0 <= nth i output 0) /\
    (exists j, (j <= i)%nat /\ nth j input 0 = nth i output 0).

Example test_case_1 : problem_9_spec [5%Z; 4%Z; 3%Z; 1%Z; 1%Z] [5%Z; 5%Z; 5%Z; 5%Z; 5%Z].
Proof.
  unfold problem_9_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    (* Destruct i to handle each index concretely, avoiding symbolic nth issues *)
    repeat (destruct i as [|i]; [| try lia]).
    all: split.
    (* For the 'forall j' part: destruct j and verify inequality *)
    all: try (intros j Hj; 
              repeat (destruct j as [|j]; [| try lia]); 
              simpl; lia).
    (* For the 'exists j' part: index 0 is always the max (5) in this case *)
    all: try (exists 0%nat; split; [lia | simpl; reflexivity]).
Qed.