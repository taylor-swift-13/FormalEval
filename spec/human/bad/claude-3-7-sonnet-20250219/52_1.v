Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [1; 2; 4; 10] 100 true.
Proof.
  unfold problem_52_spec.
  split.
  - (* -> direction *)
    intros Hall; reflexivity.
  - (* <- direction *)
    intros Htrue x Hin.
    subst.
    (* Since output = true, we must prove x < 100 for every x in the list *)
    (* We'll do a case analysis on membership in the concrete list *)
    simpl in Hin.
    destruct Hin as [Hx | Hin].
    + rewrite Hx; lia.
    + destruct Hin as [Hx | Hin].
      * rewrite Hx; lia.
      * destruct Hin as [Hx | Hin].
        -- rewrite Hx; lia.
        -- destruct Hin as [Hx | Hin].
           ++ rewrite Hx; lia.
           ++ inversion Hin.
Qed.