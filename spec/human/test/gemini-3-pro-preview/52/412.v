Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [-400; 100; -200; 300; -400; 500; -600; -600] 302 false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    assert (HIn : In 500 [-400; 100; -200; 300; -400; 500; -600; -600]).
    { simpl. right. right. right. right. right. left. reflexivity. }
    specialize (H 500 HIn).
    lia.
  - intros H.
    discriminate.
Qed.