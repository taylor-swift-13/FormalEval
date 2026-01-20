Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["467/736"; "9943/29"] -> x1=467, x2=736, n1=9943, n2=29
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 467 736 9943 29 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res implies false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Compute the values: 
       x1 * n1 = 467 * 9943 = 4643381
       x2 * n2 = 736 * 29 = 21344
       4643381 mod 21344 = 11733
       H_mod implies 11733 = 0, a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.