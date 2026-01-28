Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["16163/5588"; "1683/588"] -> x1=16163, x2=5588, n1=1683, n2=588
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 16163 5588 1683 588 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* We need to prove false = true, which is False. *)
    (* We show H_mod implies False by computing the values. *)
    vm_compute in H_mod.
    (* H_mod reduces to a contradiction like 916377 = 0 *)
    discriminate H_mod.
Qed.